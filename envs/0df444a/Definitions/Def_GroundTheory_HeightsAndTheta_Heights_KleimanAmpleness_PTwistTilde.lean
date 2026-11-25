-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistTilde
-- name    : GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistTilde
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T06:14:19.617055+00:00
-- url     : https://prove2.me/theorems/37005135-2622-5fc0-8ea5-e0caff3103f9
-- title:
--   PTwist Tilde
-- statement:
--   Definitions and structural lemmas for PTwist Tilde, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/KleimanAmpleness/PTwistTilde.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u v w
namespace TwistTildeProof
theorem smul_mem_of_mem_span {R A M : Type*} [CommRing R] [Ring A] [AddCommGroup M] [Module R A]
    [Module A M] [Module R M] [IsScalarTower R A M] [SMulCommClass A R M] {s : Set A} {t : Set M}
    {T : Submodule R M} (h : ∀ a ∈ s, ∀ b ∈ t, a • b ∈ T) {q : A} (hq : q ∈ Submodule.span R s)
    {m : M} (hm : m ∈ Submodule.span R t) : q • m ∈ T := by
  refine Submodule.span_induction (p := fun q _ => q • m ∈ T) ?_ ?_ ?_ ?_ hq
  · intro a ha
    refine Submodule.span_induction (p := fun m _ => a • m ∈ T) ?_ ?_ ?_ ?_ hm
    · exact fun b hb => h a ha b hb
    · rw [smul_zero]; exact T.zero_mem
    · intro b c _ _ hb hc; rw [smul_add]; exact T.add_mem hb hc
    · intro r b _ hb; rw [smul_comm]; exact T.smul_mem r hb
  · rw [zero_smul]; exact T.zero_mem
  · intro a b _ _ ha hb; rw [add_smul]; exact T.add_mem ha hb
  · intro r a _ ha; rw [smul_assoc]; exact T.smul_mem r ha
variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω} {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E]
  [IsScalarTower S Ω E]
def prodSet (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) (c : ℤ) :
    Set E :=
  {z | ∃ (a b : ℤ) (q : Ω) (m : E), q ∈ Q.piece a ∧ m ∈ M.piece b ∧ a + b = c ∧ z = q • m}
def prod (M : FinGradedSub (S := S) (x := x) E) (Q : FinGradedSub (S := S) (x := x) Ω) :
    FinGradedSub (S := S) (x := x) E where
  piece c := Submodule.span S (prodSet M Q c)
  smul_mem d c f m hf hm := by
    refine Submodule.span_induction (p := fun m _ => aeval x f • m ∈ Submodule.span S
      (prodSet M Q (c + d))) ?_ ?_ ?_ ?_ hm
    · rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
      refine Submodule.subset_span ⟨a, b + d, q, aeval x f • m, hq, M.smul_mem d b f m hf hm,
        by omega, ?_⟩
      rw [smul_smul, smul_smul, mul_comm]
    · rw [smul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
    · intro r a _ ha; rw [smul_comm]; exact Submodule.smul_mem _ r ha
  fg := by
    obtain ⟨n, deg, gen, hgen, hspan⟩ := M.fg
    obtain ⟨n', deg', gen', hgen', hspan'⟩ := Q.fg
    let e := (finProdFinEquiv : Fin n' × Fin n ≃ Fin (n' * n))
    refine ⟨n' * n, fun k => deg' (e.symm k).1 + deg (e.symm k).2,
      fun k => gen' (e.symm k).1 • gen (e.symm k).2, fun k => Submodule.subset_span
        ⟨_, _, _, _, hgen' _, hgen _, rfl, rfl⟩, fun c => Submodule.span_le.mpr ?_⟩
    rintro _ ⟨a, b, q, m, hq, hm, hab, rfl⟩
    refine smul_mem_of_mem_span ?_ (hspan' a hq) (hspan b hm)
    rintro _ ⟨l, f', e', hf', he', rfl⟩ _ ⟨j, f, e'', hf, he'', rfl⟩
    refine Submodule.subset_span ⟨e (l, j), f' * f, e' + e'', hf'.mul hf, ?_, ?_⟩
    · simp only [Equiv.symm_apply_apply]; push_cast; omega
    · simp only [Equiv.symm_apply_apply, smul_eq_mul, map_mul, smul_smul]
      congr 1; ring
end TwistTildeProof
end
end GroundTheory.Heights₂.Heights.Kleiman


