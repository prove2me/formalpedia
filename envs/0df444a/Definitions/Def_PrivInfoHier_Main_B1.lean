-- Prove2me | Definitions.Def_PrivInfoHier_Main_B1
-- name    : PrivInfoHier_Main_B1
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T02:14:04.339826+00:00
-- url     : https://prove2.me/theorems/0bb9e6e0-cc04-4991-bb07-13ac088c2939
-- title:
--   The App. B.1 construction: safe and unsafe mechanisms, the θ-indexed process and the filter $T_M$
-- statement:
--   Fix $\theta\in(0,1)$. Indicators $E_i\in\{s,u\}$ satisfy
--   $$P(E_i=s)=1-\theta,\qquad P(E_i=u)=\theta,\tag{B.1}$$
--   independently of the database. The **safe mechanism** $m_s$ outputs $Y_i=E_i$; the **unsafe mechanism** $m_u$ outputs $Y_i=(X,E_i)$, revealing the database exactly. The **process** sets $M_1=m_s$ and $M_{i+1}=m_s$ if $E_i=s$, $M_{i+1}=m_u$ if $E_i=u$; requests are ignored.
--
--   The **mechanism-level filter** $T_M$ stops just before the first execution of $m_u$: $T_M=\min\{k\ge0: M_{k+1}=m_u\}$, so that $\{T_M\ge t\}=\{M_1=\dots=M_t=m_s\}$.
--
--   **Formalization Note.** Outputs live in `B1Out 𝒳`, a structure with fields `db : Option 𝒳` and `e : Bool`, with the discrete σ-algebra: a safe output is `⟨none, E⟩`, an unsafe one `⟨some x, E⟩`, and `e = true` encodes $u$. `bernE θ = ofReal θ • dirac true + ofReal (1−θ) • dirac false` is (B.1). `b1Rule 𝒳 ℛ θ 0 = mSafe`, and `b1Rule (k+1) (h, r)` is `mUnsafe` if the indicator of round $k+1$ is $u$ and `mSafe` otherwise. `b1Process 𝒳 ℛ θ` is the resulting process for any database type and any request space, indexed by `θ : Set.Ioo 0 1`. `TM 𝒳 ℛ θ p = sInf {k | realisedMech (b1Process 𝒳 ℛ θ) k p = mUnsafe 𝒳 θ}`: as printed it has no horizon, and on the event that $m_u$ never runs (probability $0$ since $\theta>0$) the paper's value $+\infty$ is replaced by Lean's `sInf ∅ = 0`. Only the law of $T_M$ is used, so this changes no statement.
-- source:
--   Taylor, Vippathalla, Coon, An Information Hierarchy of Privacy Filters and Odometers, arXiv:2611.03130 (held version, sha256 77181933…), p. 17 (PDF 19), App. B.1, Eq. (B.1) and 'Mechanism-level filtering'

import Mathlib
import Definitions.Def_PrivInfoHier_Main_Model

namespace PrivInfoHier.Main

open MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- The output space of the App. B.1 process. A safe output `Y_i = E_i` is `⟨none, E_i⟩`; an unsafe
output `Y_i = (X, E_i)` is `⟨some X, E_i⟩`. The indicator `E_i ∈ {s, u}` is a `Bool`, with
`true` for `u` (unsafe next) and `false` for `s`. -/
structure B1Out (𝒳 : Type) where
  /-- the released database, if any -/
  db : Option 𝒳
  /-- the indicator `E_i`: `true` is `u`, `false` is `s` -/
  e : Bool

/-- The output space of App. B.1 carries the discrete σ-algebra. -/
instance instMeasurableSpaceB1Out (𝒳 : Type) : MeasurableSpace (B1Out 𝒳) := ⊤

/-- The law (B.1) of the indicator: `P(E_i = u) = θ`, `P(E_i = s) = 1 − θ` (`true` is `u`). -/
noncomputable def bernE (θ : Set.Ioo (0 : ℝ) 1) : Measure Bool :=
  ENNReal.ofReal θ.1 • Measure.dirac true + ENNReal.ofReal (1 - θ.1) • Measure.dirac false

instance isProbabilityMeasure_bernE (θ : Set.Ioo (0 : ℝ) 1) : IsProbabilityMeasure (bernE θ) := by
  constructor
  simp only [bernE, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add θ.2.1.le (by linarith [θ.2.2])]
  simp

/-- The safe mechanism `m_s` (App. B.1, p. 17): its output is `Y_i = E_i`, independent of `X`. -/
noncomputable def mSafe (𝒳 : Type) (θ : Set.Ioo (0 : ℝ) 1) : Mechanism 𝒳 (B1Out 𝒳) where
  law := fun _ => (bernE θ).map (fun e => (⟨none, e⟩ : B1Out 𝒳))
  isProb := fun _ => Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable

/-- The unsafe mechanism `m_u` (App. B.1, p. 17): its output is `Y_i = (X, E_i)`, revealing the
database exactly. -/
noncomputable def mUnsafe (𝒳 : Type) (θ : Set.Ioo (0 : ℝ) 1) : Mechanism 𝒳 (B1Out 𝒳) where
  law := fun x => (bernE θ).map (fun e => (⟨some x, e⟩ : B1Out 𝒳))
  isProb := fun _ => Measure.isProbabilityMeasure_map measurable_from_top.aemeasurable

/-- The release rules of App. B.1: `M_1 = m_s`, and `M_{i+1} = m_s` if `E_i = s`, `m_u` if
`E_i = u`. Requests are ignored. -/
noncomputable def b1Rule (𝒳 ℛ : Type) (θ : Set.Ioo (0 : ℝ) 1) :
    (n : ℕ) → Hist ℛ (B1Out 𝒳) n × ℛ → Mechanism 𝒳 (B1Out 𝒳)
  | 0 => fun _ => mSafe 𝒳 θ
  | k + 1 => fun hr => if (hr.1 (Fin.last k)).2.e then mUnsafe 𝒳 θ else mSafe 𝒳 θ

lemma measurable_b1Rule_law (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1) (n : ℕ)
    (x : 𝒳) : Measurable (fun h : Hist ℛ (B1Out 𝒳) n × ℛ => (b1Rule 𝒳 ℛ θ n h).law x) := by
  cases n with
  | zero => exact measurable_const
  | succ k =>
    have hb : Measurable (fun h : Hist ℛ (B1Out 𝒳) (k + 1) × ℛ => (h.1 (Fin.last k)).2.e) :=
      (measurable_from_top (f := fun y : B1Out 𝒳 => y.e)).comp
        (measurable_snd.comp ((measurable_pi_apply (Fin.last k)).comp measurable_fst))
    have hf : Measurable (fun b : Bool =>
        (if b then mUnsafe 𝒳 θ else mSafe 𝒳 θ).law x) := measurable_from_top
    have := hf.comp hb
    simpa [b1Rule, Function.comp_def, apply_ite] using this

/-- The data-release process of App. B.1 (pp. 17–18), indexed by `θ ∈ (0, 1)`. -/
noncomputable def b1Process (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1) :
    Process 𝒳 ℛ (B1Out 𝒳) where
  rule := b1Rule 𝒳 ℛ θ
  measurable_law := measurable_b1Rule_law 𝒳 ℛ θ

/-- The mechanism-level filter `T_M` of App. B.1 (p. 17), as printed: it "stops just before the
first execution of `m_u`", i.e. `T_M = min {k : M_{k+1} = m_u}`, so `{T_M ≥ t} = {M_1 = ⋯ = M_t =
m_s}`. It has no horizon. On the null event that `m_u` never runs, `sInf ∅ = 0`. -/
noncomputable def TM (𝒳 ℛ : Type) [MeasurableSpace ℛ] (θ : Set.Ioo (0 : ℝ) 1)
    (p : Path ℛ (B1Out 𝒳)) : ℕ :=
  sInf {k : ℕ | realisedMech (b1Process 𝒳 ℛ θ) k p = mUnsafe 𝒳 θ}

end PrivInfoHier.Main


