-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- name    : Formalism_MahlerMeasure_MahlerMeasureProofs_GamDeg
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:38:23.8344+00:00
-- url     : https://prove2.me/theorems/ea087640-f803-492e-b077-cd18363f9c38
-- title:
--   Gam Deg
-- statement:
--   Definitions and structural lemmas for Gam Deg, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/GamDeg.lean

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
noncomputable abbrev Dp (v : σ) : Module.End R (MvPolynomial σ R) := (pderiv v).toLinearMap
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ]
noncomputable def fw (m : σ →₀ ℕ) : ℚ_[p] := m.prod fun _ k => (k.factorial : ℚ_[p])
variable {r : ℕ} (w e : Fin r → σ)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
noncomputable def EW (w : Fin r → σ) (g : MvPolynomial σ k) : MvPolynomial σ k := ∑ c, X (w c) * pderiv (w c) g
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
noncomputable def cph (k : Type) [Field k] (A j : ℕ) : k :=
  ((-1 : k) ^ j) / (((j.factorial : k) ^ 2) * ((A.choose j : ℕ) : k))
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {k σ : Type} [Field k] [CharZero k] {r : ℕ} {w e : Fin r → σ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Polynomial Finset
section
variable {k : Type} [Field k] [CharZero k]
def IsPD (N0 d : ℕ) (g : ℕ → k) : Prop :=
  ∃ P : Polynomial k, P.natDegree ≤ d ∧ ∀ n, N0 ≤ n → g n = P.eval (n : k)
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open Finset
section
variable {k : Type} [Field k] [CharZero k]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable {R σ : Type} [CommSemiring R]
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
def lowerLast (LL : M.Letters (N + 1)) (e : ℕ) : M.Letters (N + 1) where
  vec := LL.vec
  deg := Function.update LL.deg (Fin.last N) (LL.deg (Fin.last N) - e)
end
section
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM.GammaExpansion
open MvPolynomial Finset
section
variable (p : ℕ) [Fact p.Prime] {σ : Type} [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
end
section
variable (p : ℕ) [Fact p.Prime]
end
end Formalism.GM.GammaExpansion
namespace Formalism.GM
open MvPolynomial Finset
end Formalism.GM


