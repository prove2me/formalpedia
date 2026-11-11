-- Prove2me | Definitions.Def_AgnHalfMem_truncAlive
-- name    : AgnHalfMem_truncAlive
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:13:06.7657+00:00
-- url     : https://prove2.me/theorems/8fd8b83d-3520-4c3e-88b0-d98db32de843
-- title:
--   The truncated path $\mathcal T$: events $E_v$, $E_e$, posteriors $P_{h|v}$, $P_{h|e}$, and progress $Z_i$
-- statement:
--   Fix a branching program $B$ for the learning problem of $M$ (Definition B.1). The **truncated path** $\mathcal T$ follows the computation path of $B$ but may stop early. It is defined by induction on the layers. For a vertex $v$ of layer $i$, $E_v$ is the event that $\mathcal T$ reaches $v$, $\Pr(v)=\Pr(E_v)$ (over $h$ and the samples), and $P_{h|v}$ is the law of $h$ given $E_v$. With $n=\log_2|H|$:
--
--   1. $v$ is **significant** if $\|P_{h|v}\|_2>2^{\ell}\cdot2^{-n}$;
--   2. $\mathrm{Sig}(v)=\{h'\in H: P_{h|v}(h')>2^{2\ell+2r}\cdot 2^{-n}\}$;
--   3. $\mathrm{Bad}(v)=\{x\in X: |\sum_{h'}M(x,h')P_{h|v}(h')|\ge 2^{-r'}\}$.
--
--   $\mathcal T$ stops at $v$ if $v$ is significant, or $h\in\mathrm{Sig}(v)$, or $x_{i+1}\in\mathrm{Bad}(v)$, or $v$ is a leaf; otherwise it follows the edge of $B$ selected by $(x_{i+1},y_{i+1})$. For an edge $e=(v,u)$, $E_e$ is the event that $\mathcal T$ traverses $e$, with $\Pr(e)$ and $P_{h|e}$ defined likewise. For a target vertex $s$, the progress measure is
--   $$
--   Z_i=\sum_{v\in L_i}\Pr(v)\,\langle P_{h|v},P_{h|s}\rangle^{k},
--   $$
--   where $L_i$ is the set of layer-$i$ vertices of positive probability.
--
--   **Formalization Note** Edges are pairs $(v,u)$ labelled by $A_e=\Gamma_v^{-1}(u)$. When $\Pr(v)=0$ the posterior is set to the zero function; such vertices contribute nothing to $Z_i$, which sums over all vertices of the layer. The norm and inner product are uniform-normalized; $(\cdot)^k$ is the real power.
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), App. B, pp.29–30, 33, 37

import Mathlib
import Definitions.Def_AgnHalfMem_BP
import Definitions.Def_AgnHalfMem_nrm1
import Definitions.Def_AgnHalfMem_colLaw

open MeasureTheory

namespace AgnHalfMem

variable {H X S : Type*} [Fintype H] [MeasurableSpace H] [MeasurableSpace X] {T : ℕ}

/-- The conditional law of `h` given an event `E`: `P_{h|E}(h′) = Pr(h = h′ ∧ E)/Pr(E)`
(App. B, p.29: "we denote by P_{h|v} = P_{h|E_v}, the distribution of the random variable h
conditioned on the event E_v").

**Formalization Note.** When `Pr(E) = 0` the value is `0` (Lean's `x / 0 = 0`); every claim that
conditions on `E` either assumes `Pr(E) > 0`, as the paper does, or holds trivially for the zero
function. -/
noncomputable def post {β : Type*} [MeasurableSpace β] (ν : Measure (H × β)) (E : Set (H × β))
    (h : H) : ℝ :=
  (ν (E ∩ {q | q.1 = h})).toReal / (ν E).toReal

/-- **Significant vertex** (App. B, p.29): "We say that a vertex v in layer-i of B is significant
if ‖P_{h|v}‖₂ > 2^ℓ · 2^{−n}", with `n = log₂ |H|` and the uniform-normalized norm. -/
def IsSignificant (P : H → ℝ) (l : ℝ) : Prop :=
  (2 : ℝ) ^ l * (2 : ℝ) ^ (-logCard H) < nrm2 P

/-- **Significant values** (App. B, p.29): "denote by Sig(v) the set of all h′ ∈ H, such that,
P_{h|v}(h′) > 2^{2ℓ+2r} · 2^{−n}". -/
def Sig (P : H → ℝ) (l r : ℝ) : Set H :=
  {h | (2 : ℝ) ^ (2 * l + 2 * r) * (2 : ℝ) ^ (-logCard H) < P h}

/-- **Bad edges** (App. B, p.29): "denote by Bad(v), the set of all x ∈ X, such that,
|Σ_{h′∈H} M(x, h′) · P_{h|v}(h′)| ≥ 2^{−r′}" (the printed `M(x, h)` is a typo for `M(x, h′)`,
cf. p.31). The sum is the unnormalized one, as printed. -/
def Bad (M : X → H → ℝ) (P : H → ℝ) (r' : ℝ) : Set X :=
  {x | (2 : ℝ) ^ (-r') ≤ |∑ h, M x h * P h|}

/-- The truncated path, standing at vertex `v` of layer `i` with posterior `P = P_{h|v}`, moves
along the edge `(v, u)` on the outcome `q = (h, samples)` (App. B, p.30): "The path T stops on v
if at least one of the following occurs: 1. v is significant. 2. h ∈ Sig(v). 3. x_{i+1} ∈ Bad(v).
4. v is a leaf. Otherwise, T proceeds according to the computational path of B."

**Formalization Note.** The sample read at layer `i` is `q.2 ⟨i, _⟩` (0-based, the paper's
`(x_{i+1}, y_{i+1})`); a vertex in layer `i ≥ T` is a leaf. -/
def EdgeCond (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ) (v : S) (P : H → ℝ) (u : S)
    (q : H × (Fin T → X × Bool)) : Prop :=
  ∃ hi : i < T, ¬ IsSignificant P l ∧ q.1 ∉ Sig P l r ∧ (q.2 ⟨i, hi⟩).1 ∉ Bad M P r' ∧
    b.isLeaf i v = false ∧ b.step i v (q.2 ⟨i, hi⟩) = u

/-- **The truncated path `T` (App. B, pp.29–30).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs
for Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), p.29: "We will define the truncated-path, T, to be the same as the
computation-path of a branching program B, except that it sometimes stops before reaching a leaf.
Formally, we define T, together with several other definitions and notations, by induction on the
layers of the branching program B. […] For a vertex v in layer-i of B, let E_v be the event that T
reaches vertex v."

`truncAlive μ M b ℓ r r′ i v` is the event `E_v ⊆ H × (X × Bool)^T` that the truncated path
reaches vertex `v` of layer `i`, defined by recursion on `i`; the stopping rules at layer `i` use
the posterior `P_{h|v}` of the joint law (`h` uniform, samples i.i.d. from `D_h`).

**Formalization Note.** `ℓ, r, r′` are the parameters of App. B (p.29). Edges are pairs `(v, u)`
with label `A_e = {z | step i v z = u}`. -/
noncomputable def truncAlive (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) :
    ℕ → S → Set (H × (Fin T → X × Bool))
  | 0 => fun v => {_q | v = b.start}
  | i + 1 => fun u => {q | ∃ v, q ∈ truncAlive μ M b l r r' i v ∧
      EdgeCond M b l r r' i v (post (jointLaw μ M T) (truncAlive μ M b l r r' i v)) u q}

/-- `P_{h|v}` for the vertex `v` of layer `i` (p.29). -/
noncomputable def vertexPost (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ)
    (v : S) : H → ℝ :=
  post (jointLaw μ M T) (truncAlive μ M b l r r' i v)

/-- `Pr(v) = Pr(E_v)` for the vertex `v` of layer `i` (p.29). -/
noncomputable def vertexProb (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ)
    (v : S) : ℝ :=
  (jointLaw μ M T (truncAlive μ M b l r r' i v)).toReal

/-- `E_e`, the event that `T` traverses the edge `e = (v, u)` from layer `i` to layer `i + 1`
(p.33). -/
noncomputable def truncEdge (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ)
    (v u : S) : Set (H × (Fin T → X × Bool)) :=
  {q | q ∈ truncAlive μ M b l r r' i v ∧ EdgeCond M b l r r' i v (vertexPost μ M b l r r' i v) u q}

/-- `P_{h|e}` for the edge `e = (v, u)` from layer `i` (p.33). -/
noncomputable def edgePost (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ)
    (v u : S) : H → ℝ :=
  post (jointLaw μ M T) (truncEdge μ M b l r r' i v u)

/-- `Pr(e) = Pr(E_e)` for the edge `e = (v, u)` from layer `i` (p.33). -/
noncomputable def edgeProb (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' : ℝ) (i : ℕ)
    (v u : S) : ℝ :=
  (jointLaw μ M T (truncEdge μ M b l r r' i v u)).toReal

/-- The progress measure `Z_i = Σ_{v ∈ L_i} Pr(v) · ⟨P_{h|v}, P_{h|s}⟩^k` towards the target vertex
`s` of layer `j` (p.37), with `⟨·,·⟩` uniform-normalized.

**Formalization Note.** The sum runs over all vertices of layer `i`; those with `Pr(v) = 0` (not
in `L_i`) contribute `0`. The inner products are nonnegative, and the real power `k = γk′` is
`Real.rpow`. -/
noncomputable def progressZ [Fintype S] (μ : Measure X) (M : X → H → ℝ) (b : BP S X T) (l r r' k : ℝ) (i : ℕ)
    (j : ℕ) (s : S) : ℝ :=
  ∑ v, vertexProb μ M b l r r' i v *
    (ip (vertexPost μ M b l r r' i v) (vertexPost μ M b l r r' j s)) ^ k

end AgnHalfMem


