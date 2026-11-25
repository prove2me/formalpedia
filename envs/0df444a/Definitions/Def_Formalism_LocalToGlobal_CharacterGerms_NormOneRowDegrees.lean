-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
-- name    : Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-25T00:43:19.277805+00:00
-- url     : https://prove2.me/theorems/1c632cfd-753e-4fb9-b4b1-c9efb22251dd
-- title:
--   Norm One Row Degrees
-- statement:
--   Definitions and structural lemmas for Norm One Row Degrees, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
namespace Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
namespace WeightHomogeneousMinors
section WH
variable {R : Type} [CommRing R]
end WH
section Let
variable {T : Type} (r : T → ℕ) (n : ℕ)
def wLet (σ : T) (c0 : Fin (r σ)) (ℓ : Letter T r n) : ℕ := ∑ b : Fin n, if ℓ = ⟨σ, c0, b⟩ then 1 else 0
variable {r n}
end Let
section Block
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {T : Type} {r : T → ℕ}
  {Orb : Type} {tau : Orb → Fin 2 → ZMod d → T} {o0 : Orb} {J0 : Fin 2 → Type} [∀ g, Fintype (J0 g)]
def wRow (r : T → ℕ) (tau : Orb → Fin 2 → ZMod d → T) (o0 : Orb) {N : ℕ} (g0 : Fin 2) (t0 : ZMod d) (c0 : ℕ)
    (x : Fin N × WV (IIof r tau o0)) : ℕ :=
  if x.2.1 = g0 ∧ x.2.2.1 = t0 ∧ (x.2.2.2 : ℕ) = c0 then 1 else 0
variable (X : RowData C V d (IIof r tau o0) J0) (F : Flag X)
  (hty : ∀ g (x : IIof r tau o0 g), (X.G g).ty (Sum.inl x) = x.1)
  (std : ∀ g t (c : Fin (X.rkF g t)), ((F.en g t c).2 : ℕ) = c.val)
end Block
end WeightHomogeneousMinors
end Formalism.L2.FormalSeriesBounds.RF


