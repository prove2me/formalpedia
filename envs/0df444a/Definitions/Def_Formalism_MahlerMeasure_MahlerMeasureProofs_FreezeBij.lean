-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:14:43.572685+00:00
-- url     : https://prove2.me/theorems/960eb520-61f9-4e19-89db-974bee1b7f0f
-- title:
--   Freeze Bij
-- statement:
--   Definitions and structural lemmas for Freeze Bij, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
noncomputable def evVal (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    Fin (N + 1) × Fin r → MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  fun v => Fin.lastCases (motive := fun _ => MvPolynomial (Fin N × Fin r) ℚ_[p])
    (if v.2 = ρ then 1 else 0) (fun i => X (i, v.2)) v.1
noncomputable def ev (p : ℕ) [Fact p.Prime] {N r : ℕ} (ρ : Fin r) :
    MvPolynomial (Fin (N + 1) × Fin r) ℚ_[p] →ₐ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  aeval (evVal p ρ)
noncomputable def res (m : Fin (N + 1) × Fin r →₀ ℕ) : Fin N × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => m (Fin.castSucc v.1, v.2))
noncomputable def ext (n : ℕ) (ρ : Fin r) (m : Fin N × Fin r →₀ ℕ) : Fin (N + 1) × Fin r →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => Fin.lastCases (motive := fun _ => ℕ)
    (if v.2 = ρ then n else 0) (fun i => m (i, v.2)) v.1)
end Formalism.GM.M.FB
namespace Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.M.FB
set_option linter.unusedSimpArgs false
namespace Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def wL (N r : ℕ) : Fin (N + 1) × Fin r → ℕ := fun v => if v.1 = Fin.last N then 1 else 0
end Formalism.GM.M.FB
set_option linter.unusedSimpArgs false
namespace Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
def kk (ρ : Fin r) (m : Fin (N + 1) × Fin r →₀ ℕ) : ℕ :=
  ∑ c ∈ Finset.univ.erase ρ, m (Fin.last N, c)
end Formalism.GM.M.FB
set_option linter.unusedSimpArgs false
namespace Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
end Formalism.GM.M.FB
namespace Formalism.GM
open MvPolynomial Finset M.FB
end Formalism.GM


