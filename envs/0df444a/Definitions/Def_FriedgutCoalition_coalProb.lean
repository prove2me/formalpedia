-- Prove2me | Definitions.Def_FriedgutCoalition_coalProb
-- name    : FriedgutCoalition_coalProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:34:30.584238+00:00
-- url     : https://prove2.me/theorems/0c30a7be-868e-484f-83d6-43187eaa9119
-- title:
--   Coalition probability $\mathbf P^b_S(f,\sigma)$ and influence towards an output $\mathbf J^b(f,\sigma)$
-- statement:
--   Let $\Sigma$ be a finite set, $f:\Sigma^n\to\{0,1\}$ a function and $\sigma$ a distribution on $\Sigma$. For a set $S\subseteq[n]$ of coordinates and a target $b\in\{0,1\}$, the probability that the coalition $S$ can force the output $b$ is
--
--   $$\mathbf P^b_S(f,\sigma)=\Pr_{x\sim\sigma^n}\big[\exists\, j\in\Sigma^S:\ f(j,x_{-S})=b\big],$$
--
--   where $(j,x_{-S})$ is $x$ with its coordinates in $S$ replaced by $j$. The coalition chooses $j$ after the other coordinates have been drawn. For one coordinate, $\mathbf P^b_i=\mathbf P^b_{\{i\}}$. The influence of coordinate $i$ towards $b$ and the total influence towards $b$ are
--
--   $$\mathbf J^b_i(f,\sigma)=\mathbf P^b_i(f,\sigma)-\Pr_{x\sim\sigma^n}[f(x)=b],\qquad \mathbf J^b(f,\sigma)=\sum_{i}\mathbf J^b_i(f,\sigma).$$
--
--   When $\sigma$ is omitted it is the uniform distribution. These are the quantities in which the main theorem and the direction switching lemma are stated.
--
--   **Formalization Note** All coordinates are drawn and those in $S$ are then overwritten, which gives the same probability as drawing only $x_{-S}$. The assignment $j$ ranges over all of $\Sigma^S$. The auxiliary quantity $\Pr_{x\sim\sigma^n}[f(x)=b]$ is `outProb`, and $\mathbb E_{x\sim\sigma^n}[f(x)]$ is `outProb σ f true`.
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), §2.1 "Influence towards a fixed output", p.5

import Mathlib
import Definitions.Def_FriedgutCoalition_wProb

namespace FriedgutCoalition

/-!
# Coalition probability and influence towards an output

E. Chattopadhyay, M. Gurumukhani, *A Resolution of Friedgut's Conjecture on Influential Coalitions*,
arXiv:2609.16401 (held file sha256 51f298ff…), §2.1 "Influence towards a fixed output", p.5.

For `f : Σⁿ → {0,1}`, a distribution `σ` on `Σ`, `S ⊆ [n]` and `b ∈ {0,1}`:
`P^b_S(f, σ) = Pr_{x ∼ σⁿ}[∃ j ∈ Σ^S : f(j, x_{−S}) = b]`, `P^b_i = P^b_{{i}}`,
`J^b_i(f, σ) = P^b_i(f, σ) − Pr_{x ∼ σⁿ}[f(x) = b]`, and `J^b(f, σ) = ∑_i J^b_i(f, σ)`.

**Formalization Note.** The coalition probability samples all coordinates and overwrites those in `S`
(`S.piecewise j x`). The assignment `j` is chosen inside the probability, after `x` is drawn, so the
coalition sees the other coordinates ("after the remaining coordinates are sampled", p.1). Since the
`S`-coordinates of `x` are ignored, this is the same as sampling only `x_{−S}` whenever `σ` is a
distribution. `j` ranges over all of `Σ^S`, including values `σ` gives weight zero. `{0,1}` is `Bool`.
-/

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]

/-- `P^b_S(f, σ)`: the probability, over `x ∼ σ^ι`, that some assignment `j` to the coordinates in `S`
makes `f` output `b` when the other coordinates are those of `x`. -/
noncomputable def coalProb (σ : α → ℝ) (f : (ι → α) → Bool) (S : Finset ι) (b : Bool) : ℝ :=
  wProb σ (fun x => ∃ j : ι → α, f (S.piecewise j x) = b)

/-- `Pr_{x ∼ σ^ι}[f(x) = b]`; `outProb σ f true` is `E_{x ∼ σ^ι}[f(x)]`. -/
noncomputable def outProb (σ : α → ℝ) (f : (ι → α) → Bool) (b : Bool) : ℝ :=
  wProb σ (fun x => f x = b)

/-- `J^b_i(f, σ) = P^b_i(f, σ) − Pr_{x ∼ σ^ι}[f(x) = b]`, the influence of coordinate `i` towards `b`. -/
noncomputable def towardInfl (σ : α → ℝ) (f : (ι → α) → Bool) (i : ι) (b : Bool) : ℝ :=
  coalProb σ f {i} b - outProb σ f b

/-- `J^b(f, σ) = ∑_i J^b_i(f, σ)`, the total influence towards `b`. -/
noncomputable def totalToward (σ : α → ℝ) (f : (ι → α) → Bool) (b : Bool) : ℝ :=
  ∑ i, towardInfl σ f i b

end FriedgutCoalition


