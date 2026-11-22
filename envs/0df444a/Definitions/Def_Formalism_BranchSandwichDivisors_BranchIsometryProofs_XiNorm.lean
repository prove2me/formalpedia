-- Prove2me | Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
-- name    : Formalism_BranchSandwichDivisors_BranchIsometryProofs_XiNorm
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T17:55:51.066157+00:00
-- url     : https://prove2.me/theorems/0acfa4ff-b824-4dae-b6b8-abf9113a2a85
-- title:
--   Xi Norm
-- statement:
--   Definitions and structural lemmas for Xi Norm, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BranchSandwichDivisors/BranchIsometryProofs/XiNorm.lean

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementW
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ProdFactorialSupportSubSingle
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFocksLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LFockbLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetMinor
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LBidetLemmas
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_DualWeylNonDom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL
noncomputable section
namespace Formalism.BranchingDeterminantCap
section XiA
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
def xnCof (ι : κ → Fin r) {p : ℕ} (hp : p + 1 ≤ n) (a : Fin p → κ) (j : Fin (p + 1)) :
    MvPolynomial (Fin r × Fin n) ℂ :=
  (-1) ^ (p + j.val) * (Matrix.of fun i k : Fin p =>
    (X (ι (a i), Fin.castLE hp (j.succAbove k)) : MvPolynomial (Fin r × Fin n) ℂ)).det
end XiA
section XiB
variable {r n : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
def xnMono (ι : κ → Fin r) {p : ℕ} (hp : p ≤ n) (a : Fin p → κ) : MvPolynomial (Fin r × Fin n) ℂ :=
  ∏ q : Fin p, X (ι (a q), Fin.castLE hp q)
def xnC (M : ℕ) (m : ℕ → ℕ) (p : ℕ) : ℝ := ∏ q ∈ Finset.range p, ((M : ℝ) - q + m q)
def xnSg {p : ℕ} (π : Equiv.Perm (Fin p)) : ℂ := ((Equiv.Perm.sign π : ℤ) : ℂ)
def xnN {σ : Type*} (f : MvPolynomial σ ℂ) : ℝ := (fockF f f).re
end XiB
section XiC
variable {r n : ℕ}
end XiC
section XiD
def xnT (μ : ℕ → ℕ) (i j : ℕ) : ℝ :=
  if i < j then ((μ i : ℝ) - μ j + j - i) / ((j : ℝ) - i) else 1
def xnW (N : ℕ) (μ : ℕ → ℕ) : ℝ := ∏ i ∈ Finset.range N, ∏ j ∈ Finset.range N, xnT μ i j
def xnAdd (μ : ℕ → ℕ) (p : ℕ) : ℕ → ℕ := fun j => μ j + if j < p then 1 else 0
end XiD
section XiE
variable {r n : ℕ}
structure xnInv (k : ℕ) (μ : ℕ → ℕ) (x h : MvPolynomial (Fin r × Fin n) ℂ) : Prop where
  supp : ∀ q, k ≤ q → μ q = 0
  xm : x ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hm : h ∈ dualWeyl ℂ r n (fun q => μ q.val)
  hs : h ∈ supported ℂ {v : Fin r × Fin n | v.1.val < k}
  le : xnN x ≤ xnW r μ * xnN h
end XiE
section XiF
def xnLam {n : ℕ} (lam : Fin n → ℕ) (q : ℕ) : ℕ := if h : q < n then lam ⟨q, h⟩ else 0
end XiF
end Formalism.BranchingDeterminantCap


