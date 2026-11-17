-- Prove2me | Definitions.Def_LowTempGlauber_Supplement_RandomCluster
-- name    : LowTempGlauber_Supplement_RandomCluster
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T06:26:55.174203+00:00
-- url     : https://prove2.me/theorems/5bd860e0-2527-40ad-ad4e-9a7c3e8adf30
-- title:
--   The random-cluster law $\pi_G$, the threshold $\beta_c(q,d)$, the edge density $m_c$ and the phases $E^\pm_G$
-- statement:
--   Let $G=(V,E)$ be a graph on $n$ vertices, $\beta>0$ and $q>1$. The **random-cluster law** on edge subsets $F\subseteq E$ is
--   $$\pi_G(F)\propto(e^\beta-1)^{|F|}\,q^{\kappa(F)},$$
--   where $\kappa(F)$ is the number of connected components of $(V,F)$, isolated vertices included. Its Glauber dynamics picks a uniform edge and resamples its state from $\pi_G$ conditioned on all other edges.
--
--   For $d\ge3$ and $q>2$ the critical point is
--   $$\beta_c(q,d)=\log\frac{q-2}{(q-1)^{1-2/d}-1}.$$
--   For $\beta>0$ let $B=e^\beta$, $\hat B=1+\frac{e^\beta-1}{q-1}$, $p_0=\frac{\hat B-1}{\hat B}$, $p_1=\frac{B-1}{B}$, and let $t$ be the largest solution $t>1$ of
--   $$e^\beta-1=\frac{(t-1)(t^{d-1}+q-1)}{t^{d-1}-t}.$$
--   Put $a^+=\frac{t^{d-1}}{t^{d-1}+q-1}$ and $a^-=\frac1q$. For $a\in\{a^+,a^-\}$ let $X=\hat B(1-a)^2+2a(1-a)+Ba^2$, $x_{00}=\hat B(1-a)^2/X$, $x_{11}=Ba^2/X$, and $m^\pm(\beta)=p_0x^\pm_{00}+p_1x^\pm_{11}$. The **critical edge density** is
--   $$m_c=\tfrac12\bigl(m^+(\beta_c)+m^-(\beta_c)\bigr),\qquad p_c=\tfrac d2\,m_c .$$
--   On a $d$-regular graph the **disordered** and **ordered phases** are
--   $$E^-_G=\{F:\ |F|\le\tfrac{dn}{2}m_c\},\qquad E^+_G=\{F:\ |F|>\tfrac{dn}{2}m_c\},$$
--   with phase laws $\pi^\pm_G=\pi_G(\cdot\mid E^\pm_G)$. The chain $X^+$ starts from $X^+_0=E$ and $X^-$ from $X^-_0=\emptyset$. The sampler's output encodes an edge set $F$ as the set of numbers $un+v$ over the edges $\{u,v\}\in F$ with $u<v$; its input carries $\beta$ and $q$ in real cells $0$ and $1$.
--
--   These are the objects of Theorem 2 and Theorem 21.
--
--   **Formalization Note** The law is the published random-cluster law $\propto(p/(1-p))^{|F|}q^{\kappa(F)}$ at $p=1-e^{-\beta}$, so $p/(1-p)=e^\beta-1$, and its Glauber dynamics is the published FK chain. The largest root $t$ is the supremum of the solution set; it is used only at $\beta=\beta_c$, where $t_c=(q-1)^{2/d}$ is a solution (checked in a proved sanity file) and the set is bounded.
-- source:
--   Galanis–Štefankovič, Low-Temperature Sampling via Equilibrium Disagreements, STOC 2027 submission (manuscript sha256 c41a38ff…7533d), §1.1.2 and (1), p.4; (56), p.39; Lemma 40 and Remark 41, p.42; proof of Lemma 40, p.64; p_c, p.26

import Mathlib
import Definitions.Def_PottsRapidMixing_RandomCluster
import Definitions.Def_LowTempGlauber_Supplement_FinSampler

open Classical

namespace LowTempGlauber.Supplement

/-!
# The random-cluster model at `β`, the threshold `β_c(q, d)`, the edge density `m_c` and the phases

A. Galanis, D. Štefankovič, *Low-Temperature Sampling via Equilibrium Disagreements*, STOC 2027
submission manuscript dated 3 November 2026 (held version, sha256 c41a38ff…7533d), §1.1.2 and (1), p.4;
(56), p.39; Lemma 40 and Remark 41, p.42; proof of Lemma 40, p.64; `p_c`, p.26.

**Formalization Note.**
* `rcB G β q` is `π_G(F) ∝ (e^β − 1)^{|F|} q^{κ(F)}` (p.4): the published
  `PottsRapidMixing.rcLaw G p q ∝ (p/(1−p))^{|F|} q^{κ(F)}` at `p = 1 − e^{−β}`, so `p/(1−p) = e^β − 1`.
  Configurations are `G.edgeSet → Bool`; `κ` counts components of `(V, F)` including isolated vertices.
* `betaC q d = log((q − 2)/((q − 1)^{1 − 2/d} − 1))` (p.4), real powers.
* `tLargest q d β` is "the largest solution `t > 1` of `e^β − 1 = (t−1)(t^{d−1}+q−1)/(t^{d−1}−t)`"
  (p.39, p.64), as the supremum of the solution set; it is used only at `β = β_c`, where
  `t_c = (q−1)^{2/d}` is a solution (p.64, checked in `Solutions/verification`) and the set is bounded
  (the right side tends to `∞`). Junk value `0` if the set were empty.
* `mSide q d β a = p₀ x₀₀ + p₁ x₁₁` with `B = e^β`, `B̂ = 1 + (e^β−1)/(q−1)`, `p₀ = (B̂−1)/B̂`,
  `p₁ = (B−1)/B`, `X = B̂(1−a)² + 2a(1−a) + Ba²`, `x₀₀ = B̂(1−a)²/X`, `x₁₁ = Ba²/X` ((56), Lemma 40).
  `mPlus` takes `a⁺ = t^{d−1}/(t^{d−1}+q−1)`, `mMinus` takes `a⁻ = 1/q`.
* `mC q d = ½(m⁺(β_c) + m⁻(β_c))` (Remark 41, the explicit definition of footnote 3, p.4);
  `pC q d = (d/2) m_c` (p.26).
* `IsRCPlus n d q F` is `F ∈ E⁺_G`: `|F| > (dn/2) m_c` (strict); `IsRCMinus` is `|F| ≤ (dn/2) m_c` ((1)).
* `allIn` is `X⁺₀ = E`, `allOut` is `X⁻₀ = ∅`.
* `edgeCode G F ⊆ Fin (n·n)`: the sampler's output encoding of `F`, the edge `{u, v}` with `u < v`
  numbered `u·n + v`.
-/

/-- The random-cluster law `π_G(F) ∝ (e^β − 1)^{|F|} q^{κ(F)}`, p.4. -/
noncomputable def rcB {n : ℕ} (G : SimpleGraph (Fin n)) (β q : ℝ) : (G.edgeSet → Bool) → ℝ :=
  PottsRapidMixing.rcLaw G (1 - Real.exp (-β)) q

/-- `β_c(q, d) = log((q − 2)/((q − 1)^{1 − 2/d} − 1))`, p.4. -/
noncomputable def betaC (q : ℝ) (d : ℕ) : ℝ :=
  Real.log ((q - 2) / ((q - 1) ^ (1 - 2 / (d : ℝ)) - 1))

/-- The largest `t > 1` with `e^β − 1 = (t − 1)(t^{d−1} + q − 1)/(t^{d−1} − t)` (p.39, p.64). -/
noncomputable def tLargest (q : ℝ) (d : ℕ) (β : ℝ) : ℝ :=
  sSup {t : ℝ | 1 < t ∧
    Real.exp β - 1 = (t - 1) * (t ^ (d - 1) + q - 1) / (t ^ (d - 1) - t)}

/-- `p₀ x₀₀ + p₁ x₁₁` for the vertex density `a`, (56) and Lemma 40. -/
noncomputable def mSide (q β a : ℝ) : ℝ :=
  let B := Real.exp β
  let Bh := 1 + (Real.exp β - 1) / (q - 1)
  let p₀ := (Bh - 1) / Bh
  let p₁ := (B - 1) / B
  let X := Bh * (1 - a) ^ 2 + 2 * a * (1 - a) + B * a ^ 2
  p₀ * (Bh * (1 - a) ^ 2 / X) + p₁ * (B * a ^ 2 / X)

/-- `a⁺ = t^{d−1}/(t^{d−1} + q − 1)`, p.39. -/
noncomputable def aPlus (q : ℝ) (d : ℕ) (β : ℝ) : ℝ :=
  tLargest q d β ^ (d - 1) / (tLargest q d β ^ (d - 1) + q - 1)

/-- `m⁺(β) = p₀ x⁺₀₀ + p₁ x⁺₁₁`, Lemma 40. -/
noncomputable def mPlus (q : ℝ) (d : ℕ) (β : ℝ) : ℝ := mSide q β (aPlus q d β)

/-- `m⁻(β) = p₀ x⁻₀₀ + p₁ x⁻₁₁` with `a⁻ = 1/q`, Lemma 40. -/
noncomputable def mMinus (q β : ℝ) : ℝ := mSide q β (1 / q)

/-- `m_c = ½(m⁺(β_c) + m⁻(β_c))`, Remark 41. -/
noncomputable def mC (q : ℝ) (d : ℕ) : ℝ := (mPlus q d (betaC q d) + mMinus q (betaC q d)) / 2

/-- `p_c = (d/2) m_c`, p.26. -/
noncomputable def pC (q : ℝ) (d : ℕ) : ℝ := (d : ℝ) / 2 * mC q d

/-- `F ∈ E⁺_G`: `|F| > (dn/2) m_c`, (1), p.4. -/
def IsRCPlus {n : ℕ} {G : SimpleGraph (Fin n)} (d : ℕ) (q : ℝ) (F : G.edgeSet → Bool) : Prop :=
  (d : ℝ) * n / 2 * mC q d < (PottsRapidMixing.numOpen F : ℝ)

/-- `F ∈ E⁻_G`: `|F| ≤ (dn/2) m_c`, (1), p.4. -/
def IsRCMinus {n : ℕ} {G : SimpleGraph (Fin n)} (d : ℕ) (q : ℝ) (F : G.edgeSet → Bool) : Prop :=
  (PottsRapidMixing.numOpen F : ℝ) ≤ (d : ℝ) * n / 2 * mC q d

/-- `X⁺₀ = E`, the all-in edge set. -/
def allIn {n : ℕ} (G : SimpleGraph (Fin n)) : G.edgeSet → Bool := fun _ => true

/-- `X⁻₀ = ∅`, the all-out edge set. -/
def allOut {n : ℕ} (G : SimpleGraph (Fin n)) : G.edgeSet → Bool := fun _ => false

/-- The output encoding of an edge set: `{u, v}` with `u < v` is numbered `u·n + v`. -/
noncomputable def edgeCode {n : ℕ} (G : SimpleGraph (Fin n)) (F : G.edgeSet → Bool) :
    Finset (Fin (n * n)) :=
  Finset.univ.filter (fun k => ∃ u v : Fin n, ∃ h : G.Adj u v,
    u < v ∧ F ⟨s(u, v), (SimpleGraph.mem_edgeSet G).2 h⟩ = true ∧ (k : ℕ) = (u : ℕ) * n + v)

/-- The RC sampler's initial state: the graph input, real cell `0 = β`, real cell `1 = q`. -/
noncomputable def rcInit (n d : ℕ) (G : SimpleGraph (Fin n)) (β q : ℝ) :
    SubsetConvFPRAS.State (n * n) :=
  initState (n * n) n d G (fun i => if i = 0 then β else if i = 1 then q else 0)

end LowTempGlauber.Supplement


