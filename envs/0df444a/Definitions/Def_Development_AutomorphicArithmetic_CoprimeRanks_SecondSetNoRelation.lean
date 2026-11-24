-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
-- name    : Development_AutomorphicArithmetic_CoprimeRanks_SecondSetNoRelation
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T18:12:15.154798+00:00
-- url     : https://prove2.me/theorems/92b476d2-7ff1-4b6e-8564-3587cfed07ed
-- title:
--   Second Set No Relation
-- statement:
--   Definitions and structural lemmas for Second Set No Relation, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/CoprimeRanks/SecondSetNoRelation.lean

import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_HostFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HC Formalism.BasicNotions
open scoped Pointwise
noncomputable section
namespace HostParam.Seam
structure FieldRows {φ : Frame} (H : HostRaw φ) (b : ℕ) : Prop where
  psQ : H.PsQ
  sqq : ∃ s : H.E, s ^ 2 = -(H.q : H.E) ∧ ∀ σ : H.E ≃ₐ[ℚ] H.E, σ s = ((((H.gal σ).1.1 : ℤˣ) : ℤ) : H.E) * s
  QS_exact : H.Exact
  QS_le : H.QS ≤ φ.ord ^ 2
  o_pow : φ.o ^ 64 ≤ 2 ^ φ.e
  q_ne_three : H.q ≠ 3
  split_small : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ b → jacobiSym (-(H.d : ℤ)) p = 1
  small_le : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ H.QS → 4 * l ≤ b
structure Choices (φ : Frame) (H : HostRaw φ) where
  levelPrimes : Finset ℕ
  g : Fin 2 → ℕ
  g_prime : ∀ i, (g i).Prime
  g_ne : g 0 ≠ g 1
  g_level : ∀ i, g i ∈ levelPrimes
  pde : ℕ
  pde' : ℕ
  pde_prime : pde.Prime
  pde'_prime : pde'.Prime
  pde_ne : pde ≠ pde'
  pde_level : pde ∈ levelPrimes ∧ pde' ∈ levelPrimes
  pde_mod : pde % 15 = 1 ∧ pde' % 15 = 1
  pde_ne_g : ∀ i, pde ≠ g i ∧ pde' ≠ g i
  ccK : Ideal (𝓞 H.K)
  ccK_ne_bot : ccK ≠ ⊥
  ccK_primitive : ∀ m : ℕ, 1 < m → ¬ ccK ≤ Ideal.span {(m : 𝓞 H.K)}
  ccK_split : ∀ P : Ideal (𝓞 H.K), P.IsPrime → ccK ≤ P →
    (Ideal.absNorm P).Prime ∧ jacobiSym (-(H.d : ℤ)) (Ideal.absNorm P) = 1
  ccK_coprime : ∀ p ∈ insert 2 (insert 3 (insert 5 (insert H.q (insert H.d levelPrimes)))),
    Nat.Coprime (Ideal.absNorm ccK) p
  ccK_coprimeS : Nat.Coprime (Ideal.absNorm ccK) H.QS
  level_coprimeS : ∀ p ∈ levelPrimes, Nat.Coprime p H.QS
  TT : Finset φ.A
  T2 : Finset ℕ
  u0 : φ.A
  Lw : ℕ
  two_le_Lw : 2 ≤ Lw
  second_set_range : ∀ s ∈ T2, 4 * Lw * s < φ.n0
  second_set_no_relation : NoRel T2 Lw
  CT2 : ℝ
structure HostNF (R : Ranks) where
  ax : HostAx R.toFrame
  splitBound : ℕ
  what₂ : FieldRows ax.toHostRaw splitBound
  qd_big : 4 * R.t * R.r + 1 < ax.q ∧ 4 * R.t * R.r + 1 < ax.d
  sqq : ax.E
  sqq_sq : sqq ^ 2 = -(ax.q : ax.E)
  gal_sqq : ∀ σ : ax.E ≃ₐ[ℚ] ax.E, σ sqq = ((((ax.gal σ).1.1 : ℤˣ) : ℤ) : ax.E) * sqq
  φ₀ : ax.E →+* ℂ
  φ₀_mem : φ₀ ∈ ax.toHostRaw.cmType
  𝔟 : Ideal (𝓞 ax.E)
  𝔟_spec : differentIdeal (𝓞 ax.toHostRaw.K) (𝓞 ax.E) = 𝔟 * (ax.toHostRaw.conj • 𝔟) ∧ 𝔟 ⊔ ax.toHostRaw.conj • 𝔟 = ⊤
  𝔟_stable : ∀ σ : ax.E ≃ₐ[ℚ] ax.E, ax.gal σ ∈ R.Psi → σ • 𝔟 = 𝔟
  ch : Choices R.toFrame ax.toHostRaw
def HostNF.toHost {R : Ranks} (N : HostNF R) : Formalism.BasicNotions.Host R :=
  { N.ax, N.ch with
    flPS := N.what₂.psQ, sqq := N.sqq, sqq_sq := N.sqq_sq, gal_sqq := N.gal_sqq
    QS_exact := N.what₂.QS_exact, QS_le := N.what₂.QS_le, o_pow := N.what₂.o_pow, q_ne_three := N.what₂.q_ne_three
    qd_big := N.qd_big, splitBound := N.splitBound, split_small := N.what₂.split_small, small_le := N.what₂.small_le
    φ₀ := N.φ₀, φ₀_mem := N.φ₀_mem, 𝔟 := N.𝔟, 𝔟_spec := N.𝔟_spec, 𝔟_stable := N.𝔟_stable }
def HostNF.ofHost {R : Ranks} (H : Formalism.BasicNotions.Host R) : HostNF R :=
  { ax := H.toHostAx, splitBound := H.splitBound
    what₂ := ⟨H.flPS, ⟨H.sqq, H.sqq_sq, H.gal_sqq⟩, H.QS_exact, H.QS_le, H.o_pow, H.q_ne_three, H.split_small, H.small_le⟩
    qd_big := H.qd_big, sqq := H.sqq, sqq_sq := H.sqq_sq, gal_sqq := H.gal_sqq, φ₀ := H.φ₀, φ₀_mem := H.φ₀_mem
    𝔟 := H.𝔟, 𝔟_spec := H.𝔟_spec, 𝔟_stable := H.𝔟_stable, ch := { H with } }
structure PairAt (T : HType) (X : ℝ) (q d : ℕ) : Prop where
  hyp : HostHyp q d
  log_q : T.z X / 2 < Real.log q ∧ Real.log q ≤ T.z X
  log_d : T.z' X / 2 < Real.log d ∧ Real.log d ≤ T.z' X
  split : ∀ p : ℕ, p.Prime → p ≠ 2 → (p : ℝ) ≤ T.z X → jacobiSym (-(d : ℤ)) p = 1
end HostParam.Seam
end


