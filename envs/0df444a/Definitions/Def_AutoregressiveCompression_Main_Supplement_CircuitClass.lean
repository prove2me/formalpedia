-- Prove2me | Definitions.Def_AutoregressiveCompression_Main_Supplement_CircuitClass
-- name    : AutoregressiveCompression_Main_Supplement_CircuitClass
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T21:09:52.996858+00:00
-- url     : https://prove2.me/theorems/9cdc4dc5-eaec-4527-9895-49698aa110c9
-- title:
--   The gate-bounded uniform-seed distribution class
-- statement:
--   For the fixed finite alphabet $\Sigma$, the size slice $\mathcal C^{\rm circ}_n$ consists exactly of laws $G(U_r)$ of finite deterministic sampler circuits with at most $n$ gates and at most $n$ output symbols:
--
--   $$\mathcal C^{\rm circ}_n=\{G(U_r): |G|\le n,\ \ell(G)\le n\}.$$
--
--   The sampler's distribution is constructed by evaluating its actual Boolean circuit on a uniform finite seed. Gate count is the length of the gate list in the referenced general Boolean-circuit representation; input and output wires are not gates. Gates use constants, NOT, AND and OR with fan-in at most two and unbounded fan-out. The fixed one-hot alphabet encoding agrees with the base interface. Deleting trailing output symbols changes no gate list.
--
--   A class is polynomial-size circuit samplable if some polynomial $p$ satisfies $\mathcal D_n\subseteq\mathcal C^{\rm circ}_{p(n)}$ for every $n$. This predicate records the surrounding source definition; Theorem 7.1 concerns the particular class $\mathcal C^{\rm circ}$ and Theorem 7.3 imposes no such condition on its existential classes. No gate-basis comparison or reindexing reduction is assumed as a field.
-- source:
--   Shuichi Hirahara, Mikito Nanashima, STOC 2027 submission #793 (October 2026); source.pdf, SHA-256 31e908b0cf51447e89626d9dc6d947c279aec5642ec7b320ceb07ec9b1348341; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/793.pdf, Section 7 preamble, printed pp.36–37 / PDF pp.38–39

import Mathlib
import Definitions.Def_AutoregressiveCompression_Main_Supplement_Representations

noncomputable section

namespace AutoregressiveCompression.Main.Supplement

/-- Section 7, printed pp.36–37 / PDF pp.38–39: precisely the uniform-seed
pushforwards of sampler circuits with at most n gates and at most n output
symbols. Input and output wires are not gates. No arbitrary size label is used. -/
def Ccirc (Sym : Type) [Fintype Sym] : DistributionClass Sym where
  members n := {D | ∃ (G : SamplerCode) (h : G.IsGenerator Sym),
    G.circuit.size ≤ n ∧ G.length ≤ n ∧ D = G.source h}
  length_le n D hD := by
    obtain ⟨G, h, _, hlen, rfl⟩ := hD
    exact hlen

/-- Section 7's polynomial-size samplability. This property is not an extra
hypothesis on arbitrary classes in the separation theorem. -/
def PolynomialCircuitSamplable {Sym : Type} [Fintype Sym]
    (𝒟 : DistributionClass Sym) : Prop :=
  ∃ p : Polynomial ℕ, ∀ n, 𝒟.members n ⊆ (Ccirc Sym).members (p.eval n)

end AutoregressiveCompression.Main.Supplement


