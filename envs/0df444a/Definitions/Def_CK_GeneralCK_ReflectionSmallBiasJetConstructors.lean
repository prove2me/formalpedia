-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJetConstructors
-- name    : CK_GeneralCK_ReflectionSmallBiasJetConstructors
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T15:00:11.704948+00:00
-- url     : https://prove2.me/theorems/cb0f85d7-1bde-4af7-9a59-0e16a9b483e0
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasJetConstructors` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasJetConstructors` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasJetConstructors` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasJetConstructors (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasJetConstructors.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasJet

-- ===== source module GeneralCK.ReflectionSmallBiasJetConstructors =====
section

/-! # Finite arithmetic constructors for the small-bias Taylor verifier -/

namespace GeneralCK.Reflection.SmallBiasPolynomial

def const (c : ℚ) : List Term := [⟨0, 0, 0, c⟩]
def parameter (j : ℤ) : List Term := [⟨0, 0, j, 1⟩]
def coordinateA : List Term := [⟨1, 0, 0, 1⟩]
def coordinateB : List Term := [⟨0, 1, 0, 1⟩]

@[simp] theorem eval_const (k : ℂ) (c : ℚ) (z : ℂ × ℂ) : eval k (const c) z = (c : ℂ) := by
  simp [const, eval, evalTerm]

@[simp] theorem eval_parameter (k : ℂ) (j : ℤ) (z : ℂ × ℂ) : eval k (parameter j) z = k ^ j := by
  simp [parameter, eval, evalTerm]

@[simp] theorem eval_coordinateA (k : ℂ) (z : ℂ × ℂ) : eval k coordinateA z = z.1 := by
  simp [coordinateA, eval, evalTerm]

@[simp] theorem eval_coordinateB (k : ℂ) (z : ℂ × ℂ) : eval k coordinateB z = z.2 := by
  simp [coordinateB, eval, evalTerm]

def power (n : ℕ) (p : List Term) : ℕ → List Term
  | 0 => const 1
  | m + 1 => mulTrunc n p (power n p m)

def series (n : ℕ) (coeff : ℕ → ℚ) (p : List Term) : ℕ → List Term
  | 0 => const 0
  | m + 1 => add (series n coeff p m) (scale (coeff m) (power n p m))

def logCoeff (j : ℕ) : ℚ := (-1) ^ (j + 1) / j

def logOneAdd (n : ℕ) (p : List Term) : List Term := series n logCoeff p n

def geometric (n : ℕ) (p : List Term) : List Term := series n (fun _ => 1) p n

end GeneralCK.Reflection.SmallBiasPolynomial

namespace GeneralCK.Reflection.SmallBiasJet.Approximates

open Filter Asymptotics SmallBiasPolynomial
open scoped Topology

variable {n : ℕ} {k : ℂ} {f : ℂ × ℂ → ℂ} {p : List Term}

theorem const (n : ℕ) (k : ℂ) (c : ℚ) :
    Approximates n k (fun _ => (c : ℂ)) (SmallBiasPolynomial.const c) := by
  convert exactPolynomial n k (SmallBiasPolynomial.const c) using 1
  funext z
  simp only [eval_const]

theorem parameter (n : ℕ) (k : ℂ) (j : ℤ) :
    Approximates n k (fun _ => k ^ j) (SmallBiasPolynomial.parameter j) := by
  convert exactPolynomial n k (SmallBiasPolynomial.parameter j) using 1
  funext z
  simp only [eval_parameter]

theorem coordinateA (n : ℕ) (k : ℂ) :
    Approximates n k (fun z => z.1) SmallBiasPolynomial.coordinateA := by
  convert exactPolynomial n k SmallBiasPolynomial.coordinateA using 1
  funext z
  simp only [eval_coordinateA]

theorem coordinateB (n : ℕ) (k : ℂ) :
    Approximates n k (fun z => z.2) SmallBiasPolynomial.coordinateB := by
  convert exactPolynomial n k SmallBiasPolynomial.coordinateB using 1
  funext z
  simp only [eval_coordinateB]

theorem pow (hk : k ≠ 0) (hf : Approximates n k f p) (m : ℕ) :
    Approximates n k (fun z => f z ^ m) (power n p m) := by
  induction m with
  | zero => simpa only [power, pow_zero, Rat.cast_one] using const n k 1
  | succ m ih => simpa only [power, pow_succ'] using hf.mul hk ih

theorem series (hk : k ≠ 0) (hf : Approximates n k f p) (coeff : ℕ → ℚ) (m : ℕ) :
    Approximates n k (fun z => ∑ j ∈ Finset.range m, (coeff j : ℂ) * f z ^ j)
      (SmallBiasPolynomial.series n coeff p m) := by
  induction m with
  | zero => simpa only [SmallBiasPolynomial.series, Finset.range_zero, Finset.sum_empty,
      Rat.cast_zero] using const n k 0
  | succ m ih =>
    simpa only [SmallBiasPolynomial.series, Finset.sum_range_succ] using ih.add ((hf.pow hk m).scale (coeff m))

theorem logOneAdd {n : ℕ} (hk : k ≠ 0) (hf : Approximates (n + 1) k f p) (hzero : f 0 = 0) :
    Approximates (n + 1) k (fun z => Complex.log (1 + f z))
      (SmallBiasPolynomial.logOneAdd (n + 1) p) := by
  apply hf.log_one_add hzero
  have hh := hf.series hk logCoeff (n + 1)
  convert hh using 1
  · funext z
    unfold Complex.logTaylor
    apply Finset.sum_congr rfl
    intro j hj
    simp [logCoeff]
    ring
  · rfl

theorem geometric (hk : k ≠ 0) (hf : Approximates n k f p) :
    Approximates n k (fun z => ∑ j ∈ Finset.range n, f z ^ j) (SmallBiasPolynomial.geometric n p) := by
  simpa only [Rat.cast_one, one_mul, SmallBiasPolynomial.geometric] using hf.series hk (fun _ => 1) n

end GeneralCK.Reflection.SmallBiasJet.Approximates

end


