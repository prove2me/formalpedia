-- Prove2me | Definitions.Def_CycBMWFree_Freeness_Setting
-- name    : CycBMWFree_Freeness_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:27:13.473138+00:00
-- url     : https://prove2.me/theorems/5b190e8b-112a-4e7c-b5d6-cf9f847e37dc
-- title:
--   Definition 2.13, §3.4, p. 34 — morphisms, generic parameters, and up–down tableaux
-- statement:
--   Let $S,S'$ be ground rings for cyclotomic BMW algebras of degree $r$. A ground-ring morphism $φ:S\to S'$ preserves every $δ_j$ and $u_i$, and has one of the four parameter actions
--   $$
--   (ρ,q)\mapsto(ρ',q'),\quad(ρ',-q'^{-1}),\quad(-ρ',-q'),\quad(-ρ',q'^{-1}).
--   $$
--   The generic field is $F=\mathbb Q(q,u_1,\ldots,u_r)$. Its named parameters satisfy $ρ=\prod_j u_j$ for odd $r$, $ρ=q^{-1}\prod_j u_j$ for even $r$, and $δ_a=\sum_jγ_j u_j^a$, with $γ_j$ defined by equation (3.6).
--
--   An $r$-multipartition is an $r$-tuple of Young diagrams. The shapes $Γ_n$ have total size at most $n$ and the same parity as $n$. Two shapes are adjacent when one box is added to or removed from one component. An up–down tableau of length $n$ starts with the empty shape, ends at its specified shape, and moves through $Γ_i$ at stage $i$ by adjacency. The rank target is $N(r,n)=r^n(2n-1)!!$.
--
--   These shared definitions fix the morphism and tableau conventions used by the mission's theorems. **Formalization Note** The independent variables are indexed by `Option (Fin r)`, with `none` naming $q$; the published BMW presentation uses zero-based indices for braid and contraction generators.
-- source:
--   Goodman & Hauschild Mosley, Cyclotomic BMW algebras II, arXiv:math/0612065v5, pp. 11, 19, 28–29, 34, Definition 2.13, eq. (3.6), §3.4, §4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P14

noncomputable section
open scoped BigOperators

namespace CycBMWFree.Freeness
open QAlgorithms.Papers.Independent.Support21.P14

/-- Definition 2.13, p. 11: all four permitted sign cases, with the other parameters fixed. -/
def IsGroundRingMorphism {S S' : Type*} [CommRing S] [CommRing S'] {r : ℕ}
    (P : GroundParameters S r) (P' : GroundParameters S' r) (φ : S →+* S') : Prop :=
  ((φ (P.rho : S) = (P'.rho : S') ∧
      (φ (P.q : S) = (P'.q : S') ∨ φ (P.q : S) = -((P'.q⁻¹ : S'ˣ) : S'))) ∨
    (φ (P.rho : S) = -(P'.rho : S') ∧
      (φ (P.q : S) = -(P'.q : S') ∨ φ (P.q : S) = ((P'.q⁻¹ : S'ˣ) : S')))) ∧
  (∀ j : ℕ, φ (P.delta j) = P'.delta j) ∧
  (∀ i : Fin r, φ (P.u i : S) = (P'.u i : S'))

/-- The field ℚ(q,u₁,…,uᵣ) of §3.4, pp. 28–29. -/
abbrev GenericField (r : ℕ) : Type := FractionRing (MvPolynomial (Option (Fin r)) ℚ)

/-- The independent indeterminate q. -/
def genQ (r : ℕ) : GenericField r := algebraMap (MvPolynomial (Option (Fin r)) ℚ) (GenericField r) (MvPolynomial.X none)
/-- The independent indeterminate uⱼ. -/
def genU (r : ℕ) (j : Fin r) : GenericField r := algebraMap (MvPolynomial (Option (Fin r)) ℚ) (GenericField r) (MvPolynomial.X (some j))
/-- ρ = ∏uⱼ for odd r and q⁻¹∏uⱼ for even r. -/
def genRho (r : ℕ) : GenericField r :=
  if Odd r then ∏ j, genU r j else (genQ r)⁻¹ * ∏ j, genU r j
/-- δₐ = ∑ⱼ γⱼuⱼᵃ, with γⱼ as in (3.6). -/
def genDelta (r : ℕ) (a : ℕ) : GenericField r :=
  ∑ j, gammaVector (genU r) (genRho r) (genQ r) j * genU r j ^ a
/-- The §3.4 parameter assignment, including all moments. -/
def IsGenericParameters {r : ℕ} (P : GroundParameters (GenericField r) r) : Prop :=
  (P.q : GenericField r) = genQ r ∧
  (∀ j, (P.u j : GenericField r) = genU r j) ∧
  (P.rho : GenericField r) = genRho r ∧
  ∀ a, P.delta a = genDelta r a

/-- An r-tuple of Young diagrams, p. 34. -/
abbrev Multipartition (r : ℕ) := Fin r → YoungDiagram
/-- Total number of boxes in the multipartition. -/
def mpSize {r : ℕ} (la : Multipartition r) : ℕ := ∑ i, (la i).cells.card
/-- Membership in Γₙ, p. 34. -/
def InGamma {r : ℕ} (n : ℕ) (la : Multipartition r) : Prop :=
  mpSize la ≤ n ∧ mpSize la % 2 = n % 2
/-- The shapes Γₙ, p. 34. -/
def Gamma (r n : ℕ) : Type := {la : Multipartition r // InGamma n la}
/-- One box is added to exactly one component. -/
def AddsBox {r : ℕ} (mu la : Multipartition r) : Prop :=
  ∃ i, (∀ j, j ≠ i → la j = mu j) ∧
    (mu i).cells ⊆ (la i).cells ∧ (la i).cells.card = (mu i).cells.card + 1
/-- Adjacency by addition or removal of one box. -/
def Adjacent {r : ℕ} (mu la : Multipartition r) : Prop :=
  AddsBox mu la ∨ AddsBox la mu
/-- The up–down tableaux T(n,λ), p. 34. -/
def UpDown (r n : ℕ) (la : Multipartition r) : Type :=
  {t : Fin (n + 1) → Multipartition r //
    (∀ i : Fin (n + 1), InGamma i.val (t i)) ∧
    t 0 = (fun _ => ⊥) ∧ t (Fin.last n) = la ∧
    ∀ i : Fin n, Adjacent (t i.castSucc) (t i.succ)}

/-- The proposed rank rⁿ(2n−1)!!, with value 1 at n=0. -/
def rankN (r n : ℕ) : ℕ := r ^ n * Nat.doubleFactorial (2 * n - 1)

end CycBMWFree.Freeness


