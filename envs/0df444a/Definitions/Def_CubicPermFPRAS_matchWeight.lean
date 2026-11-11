-- Prove2me | Definitions.Def_CubicPermFPRAS_matchWeight
-- name    : CubicPermFPRAS_matchWeight
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:56:11.970327+00:00
-- url     : https://prove2.me/theorems/169fdee3-e452-4814-96d4-c50c7f625e03
-- title:
--   Matching weights $\lambda(M)$, ideal hole weights $w^*$, rough anchor weights, the rescaled matrix $B$ and $W(u,v)$
-- statement:
--   For an edge-activity matrix $\lambda:V_1\times V_2\to\mathbb R$ the **weight** of a matching is $\lambda(M)=\prod_{(u,v)\in M}\lambda(u,v)$ and $\lambda(S)=\sum_{M\in S}\lambda(M)$ for a family $S$. For the input $A$ and a temperature $t\in[0,1]$, the activities are $\lambda(u,v)=1$ if $(u,v)\in E$ (that is, $A_{uv}=1$) and $\lambda(u,v)=t$ otherwise, so $\lambda(M)=t^{|M\setminus E|}$ with $0^0=1$.
--
--   1. The **ideal hole weights** are $w^*(u,v)=\lambda(\mathcal P)/\lambda(\mathcal N(u,v))$ (Eq. (3)).
--   2. Anchor weights $w(r,\cdot)$ are **$\alpha$-rough** if $1/\alpha\le w(r,v)/w^*(r,v)\le\alpha$ for every $v$ (Definition 4 restricted to the anchor row $r$).
--   3. The **rescaled matrix** of Eq. (10) is
--   $$B(u,v)=\frac{\lambda(u,v)/w(r,v)}{\sum_{v'}\lambda(u,v')/w(r,v')},$$
--   with column sums $s_v=\sum_uB(u,v)$ and the FAR multiplier $W(u,v)=1+nB(u,v)+s_v(1-B(u,v))+(s_v-B(u,v))$.
--   4. $\mu(M)=\lambda(M)/\lambda(\mathcal P)$ on $\mathcal P$ is the perfect-matching distribution; $\mathbb E_{M\sim\mu}[\lambda'(M)/\lambda(M)]$ and its second moment are the moments of the ratio estimator between two temperatures.
--   5. $A$ has a perfect matching if some permutation uses only edges of $G$.
--
--   These objects are shared by every statement of the mission.
-- source:
--   Chen, Guo, Vigoda, Yang, An Õ(n³)-time FPRAS for the Permanent, arXiv:2609.20717 (held version, sha256 9e14f335…), §4, p.6 (PDF 8); Eq. (3), p.7 (PDF 9); Definition 4, p.8 (PDF 10); Eq. (10), p.11 (PDF 13); §5.5, p.16 (PDF 18)

import Mathlib
import Definitions.Def_CubicPermFPRAS_Asg

set_option autoImplicit false

namespace CubicPermFPRAS

noncomputable section

variable {n : ℕ}

/-- **Weight of a matching** `λ(M) = ∏_{(u,v) ∈ M} λ(u,v)` for an edge-activity matrix
`λ : V₁ × V₂ → ℝ` (arXiv:2609.20717, held version sha256 9e14f335…, §4, p.6 (PDF 8); the
same product `B(M)` for the rescaled matrix, §5.1, p.11 (PDF 13)).

**Formalization Note.** For an assignment `σ` the product runs over the assigned left vertices
`u` with `σ u = some v`; unassigned vertices contribute the factor `1`. The empty product is
`1`, which gives the paper's convention `0⁰ = 1` for `λ(M) = λ^{|M \ E|}`. -/
def matchWeight (lam : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) : ℝ :=
  ∏ u, match σ u with
    | none => 1
    | some v => lam u v

/-- `λ(S) = ∑_{M ∈ S} λ(M)` for a family `S` of matchings (p.6). -/
def familyWeight (lam : Matrix (Fin n) (Fin n) ℝ) (S : Finset (Asg n)) : ℝ :=
  ∑ σ ∈ S, matchWeight lam σ

/-- The temperature activities of the input `A` at temperature `λ ∈ [0,1]` (p.6):
`λ(u,v) = 1` if `(u,v) ∈ E` (i.e. `A u v = 1`) and `λ(u,v) = λ` otherwise. -/
def tempAct (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun u v => if A u v = 1 then 1 else t

/-- The ideal hole weights `w*(u,v) = λ(P)/λ(N(u,v))`, Eq. (3), p.7 (PDF 9). -/
def idealHW (lam : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n) : ℝ :=
  familyWeight lam (PSet n) / familyWeight lam (NSet u v)

/-- `α`-rough **anchor** hole weights (Definition 4, p.8 (PDF 10), restricted to the anchor row
`r`, as the sampler and the FAR chain use only `w(r,·)`, §5, p.11 and p.15):
`1/α ≤ w(r,v)/w*(r,v) ≤ α` for every `v ∈ V₂`. -/
def IsRoughAnchor (α : ℝ) (lam : Matrix (Fin n) (Fin n) ℝ) (r : Fin n) (w : Fin n → ℝ) : Prop :=
  ∀ v, 1 / α ≤ w v / idealHW lam r v ∧ w v / idealHW lam r v ≤ α

/-- The rescaled matrix `B`, Eq. (10), p.11 (PDF 13):
`B(u,v) = (λ(u,v)/w(r,v)) / ∑_{v'} λ(u,v')/w(r,v')`. Here `w v` stands for the anchor weight
`w(r,v)`. -/
def Bmat (lam : Matrix (Fin n) (Fin n) ℝ) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun u v => (lam u v / w v) / ∑ v', lam u v' / w v'

/-- The column sum `s_v = ∑_u B(u,v)`, §5.5, p.16 (PDF 18). -/
def colSum (B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n) : ℝ := ∑ u, B u v

/-- The FAR multiplier `W(u,v) = 1 + nB(u,v) + s_v(1 − B(u,v)) + (s_v − B(u,v))`,
§5.5, p.16 (PDF 18). -/
def Wfar (B : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n) : ℝ :=
  1 + n * B u v + colSum B v * (1 - B u v) + (colSum B v - B u v)

/-- The perfect-matching distribution `µ(M) = λ(M)/λ(P)` for `M ∈ P` and `0` otherwise
(p.6, `µ_i`). -/
def muPM (lam : Matrix (Fin n) (Fin n) ℝ) (σ : Asg n) : ℝ :=
  if IsPerfect σ then matchWeight lam σ / familyWeight lam (PSet n) else 0

/-- `E_{M∼µ}[λ'(M)/λ(M)]`, the mean of the ratio estimator from temperature `λ` to `λ'`
(§4.3, p.10). -/
def ratioMean (lam lam' : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ ∈ PSet n, muPM lam σ * (matchWeight lam' σ / matchWeight lam σ)

/-- `E_{M∼µ}[(λ'(M)/λ(M))²]`, the second moment of the ratio estimator (§4.3, p.10). -/
def ratioMean2 (lam lam' : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ σ ∈ PSet n, muPM lam σ * (matchWeight lam' σ / matchWeight lam σ) ^ 2

/-- `A` (a 0/1 matrix) has a perfect matching: some permutation uses only edges of `G`. -/
def HasPM (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ p : Equiv.Perm (Fin n), ∀ i, A i (p i) = 1

instance (A : Matrix (Fin n) (Fin n) ℝ) : Decidable (HasPM A) := by
  unfold HasPM; exact Classical.dec _

end

end CubicPermFPRAS


