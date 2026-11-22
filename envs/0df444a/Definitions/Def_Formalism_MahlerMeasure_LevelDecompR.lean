-- Prove2me | Definitions.Def_Formalism_MahlerMeasure_LevelDecompR
-- name    : Formalism_MahlerMeasure_LevelDecompR
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:49.479726+00:00
-- url     : https://prove2.me/theorems/0c607997-a472-4756-b4e5-ce174ef9e0ea
-- title:
--   Level Decomp R
-- statement:
--   Definitions and structural lemmas for Level Decomp R, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/LevelDecompR.lean

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.GM.M
open MvPolynomial Finset
def LevelDecompR : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ), Function.Injective w → Function.Injective e →
    (∀ c d, w c ≠ e d) → 1 ≤ r →
    ∀ (o n : ℕ) (u : MvPolynomial σ ℚ_[p]), Formalism.GM.BiHom w e o n u →
      (∃ v : ℕ → MvPolynomial σ ℚ_[p],
        (∀ l, Formalism.GM.tieF w e (v l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v l)) ∧
        u = ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v l)) ∧
      (∀ v v' : ℕ → MvPolynomial σ ℚ_[p],
        (∀ l, Formalism.GM.tieF w e (v l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v l)) →
        (∀ l, Formalism.GM.tieF w e (v' l) = 0 ∧ Formalism.GM.BiHom w e (o - l) (n - l) (v' l)) →
        ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v l) =
          ∑ l ∈ range (min o n + 1), (Formalism.GM.tieE w e ^ l) (v' l) →
        ∀ l ≤ min o n, v l = v' l) ∧
      (∀ (l l' : ℕ) (a b : MvPolynomial σ ℚ_[p]), l ≠ l' →
        Formalism.GM.tieF w e a = 0 → Formalism.GM.BiHom w e (o - l) (n - l) a → l ≤ min o n →
        Formalism.GM.tieF w e b = 0 → Formalism.GM.BiHom w e (o - l') (n - l') b → l' ≤ min o n →
        fock p ((Formalism.GM.tieE w e ^ l) a) ((Formalism.GM.tieE w e ^ l') b) = 0)
end Formalism.GM.M


