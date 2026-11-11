-- Prove2me | Definitions.Def_LooseHamHitting_Main_Marginals
-- name    : LooseHamHitting_Main_Marginals
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T03:18:01.589195+00:00
-- url     : https://prove2.me/theorems/6fb16cf9-2e81-467e-8237-5b7f1cfa060e
-- title:
--   Random perfect matchings and random mixed Hamilton cycles: p_e, γ_e, directed edge marginals π(w; u → v), E[Φ(G, M)] and E[|C₁ ∩ C₂| − s]
-- statement:
--   A random perfect matching $F$ of a 3-graph $G$ on $V$ with an arbitrary law is a function $\mu$ on the finite set of perfect matchings of $G$ with $\mu\ge0$ and total mass $1$. Then
--   $$p_e=P[e\in F],\qquad \gamma_e=P[\exists f\in F:\ |e\cap f|\ge2].$$
--   A random $(G,M)$-respecting mixed Hamilton cycle $C$ is likewise a law $\mu$ on the set of such cycles; with a root pair $\{r_1,r_2\}\in M$ directed $r_1\to r_2$, its **directed edge marginal** is
--   $$\pi(w;u\to v)=P[C\text{ traverses }\{u,v,w\}\text{ from }u\text{ to }v\text{ with }w\text{ private, in the root orientation}].$$
--   For $G$ uniform among the $m$-edge 3-graphs on $V$ and a set $R$ of allowed triples, $E[\Phi(G\cap R,M)]$ is the average of $\Phi(G\cap R,M)$ over all $\binom{\binom{|V|}{3}}{m}$ such $G$ ($R=\binom V3$: no restriction; $R=K_M$: cycles whose triples meet $V(M)$ at most once). For a nonempty family $\mathcal C$ of cycles and $C_1,C_2$ independent and uniform on $\mathcal C$,
--   $$E[|C_1\cap C_2|-s]=\frac1{|\mathcal C|^2}\sum_{C_1,C_2\in\mathcal C}\big(|C_1\cap C_2|-s\big).$$
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 9 (Lemma 3.3(iii)); p. 17 (p_e, γ_e); p. 20 (π); p. 24 (Lemma 6.5)

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy

set_option autoImplicit false

/-!
# Laws on perfect matchings and on mixed Hamilton cycles: marginals and uniform averages

León, Liu, arXiv:2610.29894v1, p. 17 (`p_e`, `γ_e`, `F(u)`), p. 20 (directed edge marginal
`π(w; u → v)`), p. 24 (`E[|C₁ ∩ C₂| − s]`), p. 9 (expectation over a uniform `m`-edge 3-graph).

A random perfect matching `F` (resp. mixed Hamilton cycle `C`) with an arbitrary law is given by
`μ`, nonnegative on the finite set of perfect matchings (resp. cycles) and summing to `1` there.
-/

namespace LooseHamHitting.Main

noncomputable section

open Classical

variable {α : Type*}

/-- `μ` is a probability law on the finite set `S`. -/
def IsLawOn {β : Type*} (S : Finset β) (μ : β → ℝ) : Prop :=
  (∀ x ∈ S, 0 ≤ μ x) ∧ ∑ x ∈ S, μ x = 1

/-- `p_e := P[e ∈ F]` for a random perfect matching `F` of `G` on `V` with law `μ`. -/
def pmEdgeProb (V : Finset α) (G : Finset (Finset α)) (μ : Finset (Finset α) → ℝ)
    (e : Finset α) : ℝ :=
  ∑ F ∈ (perfectMatchings V G).filter (fun F => e ∈ F), μ F

/-- `γ_e := P[∃ f ∈ F : |e ∩ f| ≥ 2]` for a random perfect matching `F` with law `μ`. -/
def pmOverlapProb (V : Finset α) (G : Finset (Finset α)) (μ : Finset (Finset α) → ℝ)
    (e : Finset α) : ℝ :=
  ∑ F ∈ (perfectMatchings V G).filter (fun F => ∃ f ∈ F, 2 ≤ (e ∩ f).card), μ F

/-- Directed edge marginal `π(w; u → v) := P[C traverses {u, v, w} from u to v with w private]`
in the root orientation (root pair `{r₁, r₂}` directed `r₁ → r₂`), for a random
`(G, M)`-respecting mixed Hamilton cycle `C` with law `μ`. -/
def dirMarginal (V : Finset α) (G M : Finset (Finset α)) (μ : Finset (Finset α) → ℝ)
    (r₁ r₂ w u v : α) : ℝ :=
  ∑ C ∈ (mixedHamCycles V G M).filter (fun C => RootTraverses C r₁ r₂ {u, v, w} u v), μ C

/-- The mean of `f` under the uniform law on the nonempty finite set `S`. -/
def uniformMean {β : Type*} (S : Finset β) (f : β → ℝ) : ℝ :=
  (∑ x ∈ S, f x) / (S.card : ℝ)

/-- `E[Φ(G, M)]` for `G` uniform among the `m`-edge 3-graphs on `V`, the cycles being restricted
to the triples of `R` (take `R = \binom{V}{3}` for no restriction). -/
def expectedPhi (V : Finset α) (R M : Finset (Finset α)) (m : ℕ) : ℝ :=
  uniformMean ((V.powersetCard 3).powersetCard m) (fun G => (Phi V (G ∩ R) M : ℝ))

/-- `E[|C₁ ∩ C₂| − s]` for `C₁, C₂` independent and uniform on the family `𝒞`. -/
def overlapExcess (𝒞 : Finset (Finset (Finset α))) (s : ℕ) : ℝ :=
  (∑ C₁ ∈ 𝒞, ∑ C₂ ∈ 𝒞, (((C₁ ∩ C₂).card : ℝ) - s)) / ((𝒞.card : ℝ) ^ 2)

end

end LooseHamHitting.Main


