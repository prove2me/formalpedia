-- Prove2me | Definitions.Def_SingleSampleCombPI_XOS_Supplement_Transfer
-- name    : SingleSampleCombPI_XOS_Supplement_Transfer
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:38:45.924205+00:00
-- url     : https://prove2.me/theorems/4d669d78-6ac4-460b-a064-615853291f68
-- title:
--   Native bundle policies, subadditivity, harmonic factor and deterministic transformation
-- statement:
--   A native bundle valuation maps subsets of $m$ items to nonnegative real numbers. Normalization, monotonicity, XOS representability and subadditivity are separate predicates. Subadditivity is $v(S\cup T)\le v(S)+v(T)$. The benchmark optimizes over all pairwise disjoint bundles. Policies access the sample and revealed real prefixes and return bundles; subadditive inputs are not supplied with supporting-price or demand oracles.
--
--   For $m\ge1$, $H_m=\sum_{k=1}^m1/k$. Given any deterministic map $T$ on valuations, transformPolicy applies $T$ to each sample and each revealed real valuation and uses the original policy's chosen bundles. Existence of an appropriate XOS approximation map, its sandwich inequalities and the competitive guarantee are conclusions of Theorem A.2; none is a field of the transformation.
-- source:
--   Shuchi Chawla, Trung Dang, STOC 2027 submission #30 (October 2026), Appendix A, printed p. 36 / PDF p. 38.

import Mathlib
import Definitions.Def_SingleSampleCombPI_XOS_Online

open scoped ENNReal

namespace SingleSampleCombPI.XOS.Supplement

abbrev BundleValue (m : ℕ) := Finset (Fin m) → ℝ

def BundleValuation {m : ℕ} (v : BundleValue m) : Prop :=
  v ∅ = 0 ∧ (∀ S, 0 ≤ v S) ∧ Monotone v

def BundleXOS {m : ℕ} (v : BundleValue m) : Prop :=
  ∃ E : ComplementFreeCA.XOSGreedy.XOSExpr m, ∀ S, v S = E.val S

def BundleSubadditive {m : ℕ} (v : BundleValue m) : Prop :=
  BundleValuation v ∧ ∀ S T, v (S ∪ T) ≤ v S + v T

def bundleFeasible {n m : ℕ} (x : Fin n → Finset (Fin m)) : Prop :=
  ∀ i j, i ≠ j → Disjoint (x i) (x j)

noncomputable def bundleOpt {n m : ℕ} (r : Fin n → BundleValue m) : ℝ :=
  sSup {z | ∃ x, bundleFeasible x ∧ z = ∑ i, r i (x i)}

/-- A native valuation-only policy. In particular, subadditive types are not
required to come with supporting-price or demand oracles. -/
structure BundlePolicy (n m : ℕ) where
  Ω : Type
  seed : RandomSource Ω
  act : Ω → (Fin n → BundleValue m) → List (Fin n × BundleValue m) →
    Fin n → BundleValue m → Finset (Fin m)

def bundleRun {n m : ℕ} (S : BundlePolicy n m) (ω : S.Ω)
    (s r : Fin n → BundleValue m) (ρ : Equiv.Perm (Fin n)) : Fin n → Finset (Fin m) :=
  fun i => S.act ω s (prefixOf ρ r i) i (r i)

def BundlePolicy.Guarantee {n m : ℕ} (S : BundlePolicy n m)
    (C : BundleValue m → Prop) (α : ℝ) : Prop :=
  (∀ ω s r ρ, (∀ i, C (s i)) → (∀ i, C (r i)) →
    bundleFeasible (bundleRun S ω s r ρ)) ∧
  ∀ V : Fin n → Fin 2 → BundleValue m, (∀ i t, C (V i t)) → ∀ ρ,
    ENNReal.ofReal α * avg (fun c : Fin n → Bool =>
      ENNReal.ofReal (bundleOpt (fun i => (gogPair (V i) (c i)).2))) ≤
    pexp S.seed (fun ω => avg (fun c : Fin n → Bool =>
      let s := fun i => (gogPair (V i) (c i)).1
      let r := fun i => (gogPair (V i) (c i)).2
      ENNReal.ofReal (∑ i, r i (bundleRun S ω s r ρ i))))

noncomputable def harmonic (m : ℕ) : ℝ := ∑ k : Fin m, 1/((k.val:ℝ)+1)

/-- The same deterministic transformation is applied to both observed slots.
It is not assumed efficient; no XOS approximation oracle is an input. -/
def transformPolicy {n m : ℕ} (T : BundleValue m → BundleValue m)
    (S : BundlePolicy n m) : BundlePolicy n m where
  Ω := S.Ω
  seed := S.seed
  act := fun ω s hist i v => S.act ω (fun j => T (s j))
    (hist.map fun e => (e.1, T e.2)) i (T v)

end SingleSampleCombPI.XOS.Supplement


