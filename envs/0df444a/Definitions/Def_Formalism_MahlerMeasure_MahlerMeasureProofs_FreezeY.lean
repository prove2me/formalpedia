-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:13:49.068332+00:00
-- url     : https://prove2.me/theorems/1f2f472c-40ab-42f9-9007-c9f3b566d4b4
-- title:
--   Freeze Y
-- statement:
--   Definitions and structural lemmas for Freeze Y, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Parts
variable {N r : ℕ}
def ev (N : ℕ) (c : Fin r) : Fin (N + 1) × Fin r := (Fin.last N, c)
noncomputable def llPart (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin N × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => m (Fin.castSucc x.1, x.2))
noncomputable def etaPart (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun c => m (Fin.last N, c))
noncomputable def comb (b : Fin r →₀ ℕ) (m : Fin N × Fin r →₀ ℕ) : Fin (N + 1) × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => Fin.lastCases (b x.2) (fun i => m (i, x.2)) x.1)
end Parts
section Coeff
variable {K : Type*} [CommRing K] {N r : ℕ}
noncomputable def coeffη (b : Fin r →₀ ℕ) :
    MvPolynomial (Fin (N + 1) × Fin r) K →ₗ[K] MvPolynomial (Fin N × Fin r) K :=
  (Finsupp.lsum K (fun m : Fin (N + 1) × Fin r →₀ ℕ =>
    if etaPart m = b then (monomial (llPart m) : K →ₗ[K] MvPolynomial (Fin N × Fin r) K) else 0) :
    ((Fin (N + 1) × Fin r →₀ ℕ) →₀ K) →ₗ[K] MvPolynomial (Fin N × Fin r) K) ∘ₗ
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap
end Coeff
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset
section Coeff2
variable {K : Type*} [CommRing K] {N r : ℕ}
end Coeff2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Gl
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
variable [NeZero r]
end Gl
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Ops
variable {K : Type*} [CommRing K] {σ : Type*}
end Ops
section Rest
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
noncomputable def top (LL : Letters N) (i : Fin N) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  if LL.vec i then (LinearMap.mulLeft ℚ_[p] (X (i, c))) ∘ₗ (pderiv (i, d)).toLinearMap
  else -((LinearMap.mulLeft ℚ_[p] (X (i, d))) ∘ₗ (pderiv (i, c)).toLinearMap)
noncomputable def restAct (LL : Letters N) (j : ℕ) (c d : Fin r) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ∑ i : Fin N, if j ≤ (i : ℕ) then top p LL i c d else 0
variable [NeZero r]
end Rest
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Freeze
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Freeze
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Base
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
def emb (x : Fin N × Fin r) : Fin (N + 1) × Fin r := (Fin.castSucc x.1, x.2)
noncomputable def kill (ρ : Fin r) :
    MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] :=
  aeval (fun w => if w.1 = Fin.last N ∧ w.2 ≠ ρ then 0 else X w)
variable [NeZero r]
end Base
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
section Pol
variable {K : Type*} [CommRing K]
end Pol
section Pol2
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end Pol2
end Formalism.GM.FrozenVariableComponents
namespace Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.FrozenVariableComponents
end Formalism.GM


