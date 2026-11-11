-- Prove2me | Definitions.Def_GMMIsoSample_Main_LowerBound
-- name    : GMMIsoSample_Main_LowerBound
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:32:13.666646+00:00
-- url     : https://prove2.me/theorems/8f4130d1-4b0b-462d-a7d3-3f11451749ef
-- title:
--   Priors, prior-averaged sample laws, ε-distinguishers, Q_r^(T), M_v and A(r) (§9)
-- statement:
--   A **prior** $A$ is a probability measure on distributions over $\mathbb R^d$. Its **prior-averaged sample distribution** is
--   $$P_A^{(T)}=\mathbb E_{D\sim A}\big[D^{\otimes T}\big],$$
--   one target $D$ drawn once, then $T$ i.i.d. points from it (104). $\mathrm{Unif}(S^{d-1})$ (`unifSphere d`) is the uniform probability on the unit sphere, realised as the law of $g/\|g\|$ for $g\sim N(0,I_d)$. $Q_r^{(T)}$ (`sphereSampleLaw d T r`) draws $U\sim\mathrm{Unif}(S^{d-1})$ and then $X_1,\dots,X_T$ i.i.d. $N(rU,I_d)$. $M_v=\tfrac12N(v,I_d)+\tfrac12N(-v,I_d)$ (110), and the prior $A(r)$ (`priorSym d r`) outputs $M_{rU}$ for $U\sim\mathrm{Unif}(S^{d-1})$ (111).
--
--   For a pair of families $F_0=F(\text{false})$, $F_1=F(\text{true})$, an **$\varepsilon$-distinguisher** using $T$ sample points (Definition 43) is a randomized test (a Markov kernel to $\{0,1\}$) which, given $T$ i.i.d. points from any $D\in F_b$, outputs $b$ with probability at least $9/10$, for both $b$; Definition 43 presupposes $d_{iso}(F_0,F_1)>2\varepsilon$, which statements carry as a hypothesis.
--
--   **Formalization Note.** Priors live on `Measure (E d)` with Mathlib's Giry σ-algebra; the maps $D\mapsto D^{\otimes T}$ and $u\mapsto M_{ru}$ are measurable, so the pushforwards are genuine.
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 63, Definition 43 and (104); p. 64 (Q_r^(T)); pp. 67–68, (110)–(111)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-!
# Lower-bound objects: priors, prior-averaged sample laws, distinguishers, `Q_r^(T)`, `M_v`, `A(r)`

Chen, De, Lee, Servedio, *Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to
Isometry*, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 63
(Definition 43, (104)), p. 64 (`Q_r^(T)`), pp. 67–68 ((110), (111)).

* A prior `A` is a probability measure on distributions over `ℝ^d` (Giry σ-algebra on
  `Measure (ℝ^d)`); `priorAvg A T = E_{D∼A}[D^{⊗T}]` (104): one `D`, then `T` samples from it.
* `unifSphere d` is the uniform (rotation-invariant) probability measure on the unit sphere
  `S^{d−1}`, realised as the law of `g/‖g‖` for `g ∼ N(0, I_d)` (for `d ≥ 1`).
* An `ε`-distinguisher (Definition 43) is a Markov kernel from `T` sample points to a bit; the
  pair is `F false = F₀`, `F true = F₁`.
-/

/-- `P_A^(T) := E_{D∼A}[D^{⊗T}]` (104). -/
noncomputable def priorAvg {d : ℕ} (A : Measure (Measure (E d))) (T : ℕ) :
    Measure (Fin T → E d) :=
  A.bind (fun D => iidLaw D T)

/-- `Unif(S^{d−1})`: the law of `g/‖g‖` for `g ∼ N(0, I_d)`. -/
noncomputable def unifSphere (d : ℕ) : Measure (E d) :=
  (stdGaussian (E d)).map (fun x => ‖x‖⁻¹ • x)

/-- `Q_r^(T)` (p. 64): draw `U ∼ Unif(S^{d−1})`, set `θ = rU`, then draw `X₁, …, X_T` i.i.d.
`N(θ, I_d)`. -/
noncomputable def sphereSampleLaw (d T : ℕ) (r : ℝ) : Measure (Fin T → E d) :=
  (unifSphere d).bind (fun u => iidLaw (gauss (r • u) 1) T)

/-- `M_v := ½ N(v, I_d) + ½ N(−v, I_d)` (110). -/
noncomputable def symMix {d : ℕ} (v : E d) : Measure (E d) :=
  (1 / 2 : ℝ≥0∞) • gauss v 1 + (1 / 2 : ℝ≥0∞) • gauss (-v) 1

/-- The prior `A(r)` (p. 68): draw `U ∼ Unif(S^{d−1})` and output `M_{rU}`. -/
noncomputable def priorSym (d : ℕ) (r : ℝ) : Measure (Measure (E d)) :=
  (unifSphere d).map (fun u => symMix (r • u))

/-- An `ε`-distinguisher using `T` sample points for the pair `(F false, F true)` = `(F₀, F₁)`
(Definition 43): a randomized test that, given `T` i.i.d. points from any `D ∈ F_b`, outputs `b`
with probability at least `9/10`, for both `b`. (Definition 43 presupposes
`d_iso(F₀, F₁) > 2ε`; statements using it carry that hypothesis.) -/
def IsDistinguisher {d : ℕ} (F : Bool → Set (Measure (E d))) (T : ℕ)
    (κ : Kernel (Fin T → E d) Bool) : Prop :=
  IsMarkovKernel κ ∧ ∀ b : Bool, ∀ D ∈ F b, (9 / 10 : ℝ≥0∞) ≤ (iidLaw D T).bind κ {b}

end GMMIsoSample.Main


