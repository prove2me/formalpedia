-- Prove2me | Definitions.Def_OAI_InformationTheory_PhotonNumber_Inequality
-- name    : OAI_InformationTheory_PhotonNumber_Inequality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-16T00:52:28.941281+00:00
-- url     : https://prove2.me/theorems/5cbe3b5f-d6ec-4b27-87be-1867fd4c1024
-- title:
--   Thermal-interior parameters, beam-splitter regularization and number-cutoff states for $n$ bosonic modes
-- statement:
--   Throughout, $n\in\mathbb{N}$ is the number of bosonic modes, $\mathcal{F}_n=\ell^2(\mathbb{N}^n;\mathbb{C})$ is the full Fock space with orthonormal number basis $\{|k\rangle : k\in\mathbb{N}^n\}$, and $\rho_{kl}=\langle k|\rho|l\rangle$ denotes a matrix entry. A *state* is a positive bounded operator $\rho$ on $\mathcal{F}_n$ whose diagonal series converges with $\sum_{k}\operatorname{Re}\rho_{kk}=1$. The thermal entropy per mode is $g(t)=(t+1)\log(t+1)-t\log t$, and $g^{-1}(s)=\inf\{t\ge 0 : g(t)\ge s\}$. The module defines the following objects.
--
--   1. **Thermal-interior parameters.** A record $T=(\eta,\theta,d,r_1,r_2)$ with $\eta,\theta\in(0,1)$ and $d,r_1,r_2>0$. From it one defines
--   $$a=\theta\big(\eta r_1+(1-\eta)r_2\big),\qquad b=a+\theta,\qquad r_0=a+(1-\theta)d,$$
--   which are all positive, the cap $c=\min\{(1-\theta)d/a,\ (1-\theta)(d+1)/b\}>0$, and for every $m\in\mathbb{N}$
--   $$\varepsilon_m=\min\Big\{c,\ \frac{1}{m+1}\Big\},\qquad \kappa_m=\min\Big\{\frac{1}{m+2},\ \frac{\varepsilon_m^2}{4(\varepsilon_m+2)\,M(r_0)^2}\Big\},$$
--   which satisfy $\varepsilon_m>0$ and $0<\kappa_m<1$. Here $M(r)=\big(h(r)\,\underline{w}(r)\big)^{-1/2}$ is the positive mixture constant of the thermal metric, with $h(r)=\log(r+1)-\log r$ and $\underline{w}(r)$ the infimum of an explicit auxiliary weight function, which satisfies $\underline{w}(r)\ge r$ for $r>0$. The $m$-th *setup* is the thermal regularization package with parameters $(\eta,\theta,\kappa_m,\varepsilon_m,d,r_1,r_2)$; its required slack conditions $(1+\varepsilon_m)a\le r_0$, $(1+\varepsilon_m)b\le r_0+1$ and $\kappa_m\le \varepsilon_m^2/(4(\varepsilon_m+2)M(r_0)^2)$ are verified from the choice of $c$ and $\kappa_m$.
--
--   2. **Raw regularized output.** For states $\rho,\sigma$ on $n$ modes,
--   $$\operatorname{raw}_T(\rho,\sigma)=\mathcal{B}_\theta\big(\mathcal{B}_\eta(\rho,\sigma),\ \tau_d\big),$$
--   where $\mathcal{B}_\eta(\rho,\sigma)$ is the beam-splitter output state: $\rho\otimes\sigma$ is sent through the passive beam splitter of transmissivity $\eta$, which in every mode transforms the input creation operators $a^\dagger,b^\dagger$ into output creation operators $c^\dagger,d^\dagger$ via $a^\dagger\mapsto\sqrt{\eta}\,c^\dagger-\sqrt{1-\eta}\,d^\dagger$ and $b^\dagger\mapsto\sqrt{1-\eta}\,c^\dagger+\sqrt{\eta}\,d^\dagger$, and the $d$-port is traced out. Further, $\tau_d$ is the $n$-mode thermal state of mean photon number $d$ per mode, the number-diagonal state with $\langle k|\tau_d|k\rangle=\prod_{j=1}^n \frac{1}{d+1}\big(\frac{d}{d+1}\big)^{k_j}$.
--
--   3. **Interior transmissivities.** The sequence $\eta_m=1-\frac{1}{m+2}$, $m\in\mathbb{N}$.
--
--   4. **Number cutoff.** For a state $\rho$ and a finite set $F\subset\mathbb{N}^n$: the captured mass $\mu_F(\rho)=\sum_{k\in F}\operatorname{Re}\rho_{kk}$, which satisfies $\mu_F(\rho)\le 1$; the coordinate projection $P_F=\sum_{k\in F}|k\rangle\langle k|$; the compression $P_F\rho P_F$, which is positive and has diagonal entries $\rho_{kk}$ for $k\in F$ and $0$ for $k\notin F$; the vacuum projector $|0\rangle\langle 0|$; and the cutoff state
--   $$\rho_F=P_F\,\rho\,P_F+\big(1-\mu_F(\rho)\big)\,|0\rangle\langle 0|,$$
--   which is shown to be a state (positive with unit trace).
--
--   5. **Shifted reference value.** For $a\in\mathbb{R}$ and $m\in\mathbb{N}$, the number $a+\frac{1}{m+1}$.
--
--   The module also records basic facts about $g$: $g(0)=0$; $g$ is continuous; $g'(t)=\log(t+1)-\log t$ for $t>0$; $g$ is strictly increasing on $[0,\infty)$; $g^{-1}(g(t))=t$ for every $t\ge 0$; and $g^{-1}(0)=0$.
--
--   These objects organize an approximation scheme for entropy inequalities of beam-splitter outputs: the thermal-interior parameters and the raw output describe inputs mixed with a thermal state so that all quantities stay strictly inside the thermal regime, with tolerances $\varepsilon_m,\kappa_m$ shrinking as $m$ grows, while the number cutoff replaces a state by one supported on finitely many number states plus a vacuum correction that restores unit trace.
--
--   **Formalization Note** The parameter record is the Lean structure `ThermalInterior`, and `setup m` produces a `ThermalSetup`. The function $g$ is defined on all of $\mathbb{R}$ using Lean's convention $\log 0=0$, so $g(0)=0$ without a separate case, and `gInv` is an `sInf`; only its values on $[0,\infty)$ are relevant. The private lemma `ite_eq_right` is a backport helper.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/PhotonNumber/Inequality.lean

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Inequality.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the EntropyPhotonNumber mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy
import Definitions.Def_OAI_InformationTheory_PhotonNumber_GibbsVariational
import Definitions.Def_OAI_Analysis_Herglotz
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Interpolation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Contraction
import Definitions.Def_OAI_InformationTheory_PhotonNumber_FiniteVariation
import Definitions.Def_OAI_InformationTheory_PhotonNumber_PhysicalMinimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Duality
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Minimum
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalLimit

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

section
open scoped BigOperators ComplexConjugate Topology
open Filter

namespace HilbertBasis
open scoped _root_.HilbertBasis
variable {I E A : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

end HilbertBasis

namespace EntropyPhotonNumber
open QuantumTrace TensorLp

end EntropyPhotonNumber

end

namespace EntropyPhotonNumber
open scoped BigOperators Topology

open Set Filter ThermalMetric

@[simp] theorem g_zero : g 0 = 0 := by simp [g]

theorem continuous_g : Continuous g := by
  have h : g = fun t : ℝ => Real.negMulLog t - Real.negMulLog (t + 1) := by
    funext t
    simp only [g, Real.negMulLog_def]
    ring
  rw [h]
  exact Real.continuous_negMulLog.sub
    (Real.continuous_negMulLog.comp (continuous_id.add continuous_const))

theorem hasDerivAt_g {t : ℝ} (ht : 0 < t) :
    HasDerivAt g (Real.log (t + 1) - Real.log t) t := by
  have h₁ := Real.hasDerivAt_negMulLog (ne_of_gt ht)
  have h₂ := (Real.hasDerivAt_negMulLog (ne_of_gt (by linarith : 0 < t + 1))).comp t
    ((hasDerivAt_id t).add_const 1)
  convert! h₁.sub h₂ using 1
  · funext x
    simp only [g, Real.negMulLog_def, Pi.sub_apply, Function.comp_apply, id_eq]
    ring
  · ring

theorem strictMonoOn_g : StrictMonoOn g (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0) continuous_g.continuousOn
  intro x hx
  rw [interior_Ici, mem_Ioi] at hx
  rw [(hasDerivAt_g hx).deriv]
  exact sub_pos.mpr (Real.strictMonoOn_log hx
    (show 0 < x + 1 by linarith) (show x < x + 1 by linarith))

theorem gInv_g {t : ℝ} (ht : 0  ≤  t) : gInv (g t) = t := by
  apply csInf_eq_of_forall_ge_of_forall_gt_exists_lt (s := {u : ℝ | 0  ≤  u ∧ g t  ≤  g u})
  · exact ⟨t, ht, le_rfl⟩
  · intro u hu
    by_contra h
    have hlt := strictMonoOn_g hu.1 ht (lt_of_not_ge h)
    exact (not_lt_of_ge hu.2) hlt
  · intro w hw
    exact ⟨t, ⟨ht, le_rfl⟩, hw⟩

@[simp] theorem gInv_zero : gInv 0 = 0 := by simpa using gInv_g (t := 0) le_rfl

end EntropyPhotonNumber

open scoped BigOperators ComplexConjugate Topology

namespace EntropyPhotonNumber

section
open QuantumTrace ThermalMetric Filter

structure ThermalInterior where
  η : ℝ
  θ : ℝ
  d : ℝ
  r1 : ℝ
  r2 : ℝ
  hη : η ∈ Set.Ioo 0 1
  hθ : θ ∈ Set.Ioo 0 1
  hd : 0<d
  hr1 : 0<r1
  hr2 : 0<r2

namespace ThermalInterior
variable (T : ThermalInterior)
def a : ℝ := T.θ*(T.η*T.r1+(1-T.η)*T.r2)
def b : ℝ := T.a+T.θ
def r0 : ℝ := T.a+(1-T.θ)*T.d
theorem a_pos : 0<T.a := mul_pos T.hθ.1
  (add_pos (mul_pos T.hη.1 T.hr1) (mul_pos (sub_pos.mpr T.hη.2) T.hr2))
theorem b_pos : 0<T.b := add_pos T.a_pos T.hθ.1
theorem r0_pos : 0<T.r0 := add_pos T.a_pos (mul_pos (sub_pos.mpr T.hθ.2) T.hd)
def cap : ℝ := min ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b)
theorem cap_pos : 0<T.cap := lt_min
  (div_pos (mul_pos (sub_pos.mpr T.hθ.2) T.hd) T.a_pos)
  (div_pos (mul_pos (sub_pos.mpr T.hθ.2) (by linarith [T.hd])) T.b_pos)
def eps (m : ℕ) : ℝ := min T.cap (1/((m:ℝ)+1))
theorem eps_pos (m : ℕ) : 0<T.eps m := lt_min T.cap_pos (by positivity)
def kap (m : ℕ) : ℝ := min (1/((m:ℝ)+2))
  (T.eps m^2/(4*(T.eps m+2)*mixtureConstant T.r0^2))
theorem kap_pos (m : ℕ) : 0<T.kap m := by
  apply lt_min
  · positivity
  · exact div_pos (sq_pos_of_pos (T.eps_pos m)) (mul_pos
      (mul_pos (by norm_num) (by linarith [T.eps_pos m])) (sq_pos_of_pos (mixtureConstant_pos T.r0_pos)))
theorem kap_lt_one (m : ℕ) : T.kap m<1 := by
  apply (min_le_left _ _).trans_lt
  exact (div_lt_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
def setup (m : ℕ) : ThermalSetup where
  η := T.η
  θ := T.θ
  κ := T.kap m
  ε := T.eps m
  d := T.d
  r1 := T.r1
  r2 := T.r2
  hη := T.hη
  hθ := T.hθ
  hκ := ⟨T.kap_pos m,T.kap_lt_one m⟩
  hε := T.eps_pos m
  hd := T.hd
  hr1 := T.hr1
  hr2 := T.hr2
  slack_r := by
    have hh := (min_le_left T.cap (1/((m:ℝ)+1))).trans
      (min_le_left ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b))
    have hm := (le_div_iff₀ T.a_pos).mp hh
    change T.eps m*T.a≤(1-T.θ)*T.d at hm
    dsimp [a] at hm
    nlinarith
  slack_s := by
    have hh := (min_le_left T.cap (1/((m:ℝ)+1))).trans
      (min_le_right ((1-T.θ)*T.d/T.a) ((1-T.θ)*(T.d+1)/T.b))
    have hm := (le_div_iff₀ T.b_pos).mp hh
    change T.eps m*T.b≤(1-T.θ)*(T.d+1) at hm
    dsimp [b,a] at hm
    nlinarith
  small_κ := min_le_right _ _

def raw {n : ℕ} (ρ σ : State n) : State n :=
  beamOutput T.θ ⟨T.hθ.1.le,T.hθ.2.le⟩
    (beamOutput T.η ⟨T.hη.1.le,T.hη.2.le⟩ ρ σ) (thermalState n T.d T.hd)

end ThermalInterior
end

section
open QuantumTrace FischerBeam TensorLp MvPolynomial

end

section
open QuantumTrace ThermalMetric Filter

def interiorTransmission (m : ℕ) : ℝ := 1-1/((m:ℝ)+2)
end

namespace NumberCutoff
open QuantumTrace Filter InnerProductSpace

variable {n : ℕ} (ρ : State n) (F : Finset (NumberIndex n))
def mass : ℝ := ∑ k ∈ F, (entry ρ.op k k).re
def projection : Fock n →L[ℂ] Fock n := basisProjection (numberBasis n) F
def compressed : Fock n →L[ℂ] Fock n := projection F ∘L ρ.op ∘L projection F
def vacuum : Fock n →L[ℂ] Fock n := rankOne ℂ (numberKet (0:NumberIndex n)) (numberKet 0)

theorem mass_le_one : mass ρ F≤1 := by
  apply (ρ.trace_one.summable.sum_le_tsum F (fun k _ => ρ.positive.re_inner_nonneg_right (numberKet k))).trans_eq
  exact ρ.trace_one.tsum_eq

theorem compressed_positive : (compressed ρ F).IsPositive := by
  have hh := ρ.positive.adjoint_conj (projection F)
  simpa only [compressed, projection,basisProjection_adjoint] using hh

theorem compressed_diagonal (k : NumberIndex n) :
    entry (compressed ρ F) k k=if k∈F then entry ρ.op k k else 0 := by
  classical
  unfold entry compressed
  rw [← numberBasis_apply n k]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.adjoint_inner_left,projection,basisProjection_adjoint,
    basisProjection_apply_basis]
  split_ifs <;> simp

theorem vacuum_diagonal (k : NumberIndex n) : entry (vacuum (n:=n)) k k=if k=0 then 1 else 0 := by
  classical
  simp only [vacuum,entry,rankOne_apply,inner_smul_right,← numberBasis_apply,
    orthonormal_iff_ite.mp (numberBasis n).orthonormal]
  split_ifs <;> simp_all

def state : State n where
  op := compressed ρ F+((1-mass ρ F:ℝ):ℂ) • vacuum
  positive := (compressed_positive ρ F).add
    ((isPositive_rankOne_self (numberKet (0:NumberIndex n))).smul_of_nonneg
      (by exact_mod_cast sub_nonneg.mpr (mass_le_one ρ F)))
  trace_one := by
    classical
    have h1 : HasSum (fun k => if k∈F then (entry ρ.op k k).re else 0) (mass ρ F) := by
      simpa only [mass, Finset.sum_ite_mem, Finset.inter_self] using
        (hasSum_sum_of_ne_finset_zero (s:=F) (f:=fun k => if k∈F then (entry ρ.op k k).re else 0)
          (by intro k hk; simp only [ite_eq_right hk]))
    have h2 : HasSum (fun k : NumberIndex n => if k=0 then 1-mass ρ F else 0) (1-mass ρ F) :=
      hasSum_ite_eq 0 _
    convert! h1.add h2 using 1
    · funext k
      simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
      change (entry (compressed ρ F) k k+((1-mass ρ F:ℝ):ℂ)*entry vacuum k k).re=_
      rw [compressed_diagonal,vacuum_diagonal]
      split_ifs <;> simp [entry]
    · ring

end NumberCutoff

open QuantumTrace ThermalMetric Filter

def positiveReference (a : ℝ) (m : ℕ) : ℝ := a+1/((m:ℝ)+1)
end EntropyPhotonNumber

end

end OAI


