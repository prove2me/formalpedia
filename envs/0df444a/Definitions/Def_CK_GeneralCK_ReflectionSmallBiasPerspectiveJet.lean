-- Prove2me | Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPerspectiveJet
-- name    : CK_GeneralCK_ReflectionSmallBiasPerspectiveJet
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T22:59:15.445651+00:00
-- url     : https://prove2.me/theorems/6015084a-f7a7-4908-9e07-cd7e87fc5cf0
-- title:
--   Courtade–Kumar proof module `GeneralCK.ReflectionSmallBiasPerspectiveJet` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.ReflectionSmallBiasPerspectiveJet` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.ReflectionSmallBiasPerspectiveJet` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.ReflectionSmallBiasPerspectiveJet (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/ReflectionSmallBiasPerspectiveJet.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasContactTable

-- ===== source module GeneralCK.ReflectionSmallBiasPerspectiveJet =====
section

/-! Direct finite expansion of the entropy perspective contact value. -/

namespace GeneralCK.Reflection.SmallBiasPerspectiveJet

open Filter Asymptotics SmallBiasPolynomial SmallBiasJet
open scoped Topology

noncomputable def evalContactTerm (k : ℂ) (t : Term) (s e : ℂ) : ℂ :=
  (t.c:ℂ)*k^t.k*s^t.a*(e⁻¹)^(t.a-1)

noncomputable def evalContact (k : ℂ) : List Term → ℂ → ℂ → ℂ
  | [], _, _ => 0
  | t :: ts, s, e => evalContactTerm k t s e + evalContact k ts s e

theorem mul_div_pow (s e : ℂ) {n : ℕ} (hn : 2≤n) :
    e*(s/e)^n = s^n*(e⁻¹)^(n-1) := by
  by_cases he : e=0
  · simp [he,show n ≠ 0 by omega,show n-1 ≠ 0 by omega]
  · have hn1 : n-1+1=n := by omega
    calc
      _ = s^n*(e*(e⁻¹)^n) := by rw [div_pow,div_eq_mul_inv,← inv_pow]; ring
      _ = s^n*(e*((e⁻¹)^(n-1)*e⁻¹)) := by rw [← pow_succ,hn1]
      _ = s^n*(e⁻¹)^(n-1) := by
        rw [mul_left_comm e, mul_inv_cancel₀ he, mul_one]

theorem evalContactTerm_eq (k : ℂ) (t : Term) (s e : ℂ) (hn : 2≤t.a) (hb : t.b=0) :
    e*evalTerm k t (s/e,0) = evalContactTerm k t s e := by
  unfold evalTerm evalContactTerm
  simp only [hb,pow_zero,mul_one]
  calc
    _ = (t.c:ℂ)*k^t.k*(e*(s/e)^t.a) := by ring
    _ = _ := by rw [mul_div_pow s e hn]; ring

theorem evalContact_eq (k : ℂ) (ts : List Term) (s e : ℂ)
    (ht : ∀ t ∈ ts, 2≤t.a ∧ t.b=0) :
    e*eval k ts (s/e,0) = evalContact k ts s e := by
  induction ts with
  | nil => simp [eval,evalContact]
  | cons t ts ih =>
    have htop := ht t (by simp)
    have htail := ih (fun r hr => ht r (by simp [hr]))
    simp only [eval,evalContact,mul_add,evalContactTerm_eq k t s e htop.1 htop.2,htail]

theorem evalContact_append (k : ℂ) (ps qs : List Term) (s e : ℂ) :
    evalContact k (ps++qs) s e = evalContact k ps s e+evalContact k qs s e := by
  induction ps with
  | nil => simp [evalContact]
  | cons t ts ih => simp [evalContact,ih,add_assoc]

theorem contactValue_of_finite {k : ℂ} {s e : ℂ × ℂ → ℂ} {ts q : List Term}
    (hs : AnalyticAt ℂ s 0) (he : AnalyticAt ℂ e 0) (hs0 : s 0=0) (he0 : e 0≠0)
    (hphi : Approximates 24 k (fun z => SmallBiasContactValueJet.phi z.1) ts)
    (hts : ∀ t ∈ ts, 2≤t.a ∧ t.b=0)
    (ht : Approximates 24 k (fun z => evalContact k ts (s z) (e z)) q) :
    Approximates 24 k (fun z => SmallBiasComplexDomain.contactValue (s z) (e z)) q := by
  have ha : AnalyticAt ℂ (fun z => SmallBiasComplexDomain.contactValue (s z) (e z)) 0 :=
    (SmallBiasComplexDomain.analyticAt_contactValue (p := (s 0,e 0)) he0
      (by simp [hs0])).comp_of_eq (hs.prod he) rfl
  have hratio : AnalyticAt ℂ (fun z => (s z/e z,(0:ℂ))) 0 :=
    (hs.div he he0).prod analyticAt_const
  have hz : (s 0/e 0,(0:ℂ)) = (0:ℂ × ℂ) := by simp [hs0]
  have hT : Tendsto (fun z => (s z/e z,(0:ℂ))) (𝓝 (0:ℂ × ℂ)) (𝓝 0) := by
    simpa only [hz] using hratio.continuousAt.tendsto
  have hnorm : (fun z => (s z/e z,(0:ℂ))) =O[𝓝 (0:ℂ × ℂ)] (fun z => ‖z‖) := by
    simpa only [hz,sub_zero] using hratio.differentiableAt.isBigO_sub.norm_right
  have herror := (hphi.error.comp_tendsto hT).trans (hnorm.norm_left.pow 24)
  have hE : e =O[𝓝 (0:ℂ × ℂ)] (fun _ => (1:ℝ)) := he.continuousAt.tendsto.isBigO_one ℝ
  have hm := hE.mul herror
  have hne : ∀ᶠ z in 𝓝 (0:ℂ × ℂ), e z≠0 := he.continuousAt.eventually_ne he0
  have heq : (fun z => e z*(SmallBiasContactValueJet.phi (s z/e z)-eval k ts (s z/e z,0))) =ᶠ[𝓝 0]
      (fun z => SmallBiasComplexDomain.contactValue (s z) (e z)-evalContact k ts (s z) (e z)) := by
    filter_upwards [hne] with z hz'
    rw [← evalContact_eq k ts (s z) (e z) hts]
    unfold SmallBiasContactValueJet.phi SmallBiasComplexDomain.contactValue
    field_simp [hz']
    <;> ring
  apply ht.transfer ha
  simpa only [one_mul] using hm.congr' heq Filter.EventuallyEq.rfl

end GeneralCK.Reflection.SmallBiasPerspectiveJet


end


