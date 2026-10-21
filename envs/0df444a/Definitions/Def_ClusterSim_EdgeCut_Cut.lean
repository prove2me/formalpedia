-- Prove2me | Definitions.Def_ClusterSim_EdgeCut_Cut
-- name    : ClusterSim_EdgeCut_Cut
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T05:53:05.218023+00:00
-- url     : https://prove2.me/theorems/c0f590c1-2138-445b-a9da-f46079877096
-- title:
--   The cut network (G′, A_s): every edge uv of a set C is replaced by u → ▷(O_{s_e}) and ◁(ρ_{s_e}) → v; the coefficient c_s of eq. (32) (pp. 8–9)
-- statement:
--   Let $(G,\mathcal A)$ be a tensor network, $C$ a finite set of its edges, and $s=(s_e)_{e\in C}\in[8]^C$ a choice of one of the eight cases of eqs. (12)–(19) for every edge of $C$. The **cut network** $(G',\mathcal A_s)$ is obtained by cutting each edge $e=uv\in C$ and mending its two ends:
--   $$u\to v\quad\Longrightarrow\quad u\to\ \triangleright(O_{s_e})\qquad \triangleleft(\rho_{s_e})\to v .$$
--
--   1. **Vertices.** The original vertices, plus for every $e\in C$ a new observable vertex $\triangleright_e$ carrying the tensor $_\beta A(O_{s_e})=\operatorname{Tr}[M(\beta)O_{s_e}]$ of eq. (7), and a new state vertex $\triangleleft_e$ carrying the tensor $A(\rho_{s_e})_\beta=\operatorname{Tr}[\rho_{s_e}M(\beta)^\dagger]$ of eq. (5).
--   2. **Edges.** Every original edge $e$ is kept; for $e\in C$ it now ends at $\triangleright_e$ instead of $v=\mathrm{tgt}(e)$. For every $e\in C$ there is one new edge $\triangleleft_e\to v$.
--   3. **Tensors of the original vertices.** They are unchanged, except that the target $v$ of a cut edge $e$ reads the index of the new edge $\triangleleft_e\to v$ where it used to read that of $e$.
--
--   So the qubit produced at $u$ is measured with the observable $O_{s_e}$, and the qubit required at $v$ is supplied in the state $\rho_{s_e}$ (proof of Lemma 1, p. 9). The coefficient attached to $s$ is eq. (32),
--   $$c_s=\prod_{e\in C}c_{s_e}.$$
--
--   For a single edge ($C=\{e\}$, $s\equiv i$) this is the network $(G',\mathcal A_i)$ of Lemma 1; for $C=E_{\mathrm{cut}}$ it is the network $(G',\mathcal A_s)$ of the proof of Theorem 1.
--
--   **Formalization Note** The vertex type is $V\oplus(C\oplus C)$ (`inr (inl e)` is $\triangleright_e$, `inr (inr e)` is $\triangleleft_e$) and the edge type is $E\oplus C$ (`inl e` the original edge, `inr e` the new edge $\triangleleft_e\to\mathrm{tgt}(e)$). The cut is defined for a whole set $C$ at once, so Lemma 1 is the singleton case. Only the target vertex is rerouted, which makes the cut identity hold for arbitrary, not necessarily local, tensors. $s_e\in$ `Fin 8` is the paper's $s_e-1$.
-- source:
--   Peng, Harrow, Ozols & Wu, Simulating Large Quantum Circuits on a Small Quantum Computer, arXiv:1904.00102v2, pp. 8–9, Lemma 1 and its proof (Supplemental Material §III), and proof of Theorem 1, eqs. (31)–(32)

import Mathlib
import Definitions.Def_ClusterSim_EdgeCut_TensorNetwork
import Definitions.Def_ClusterSim_EdgeCut_PauliData

namespace ClusterSim.EdgeCut

noncomputable section

/-- The cut network `(G′, A_s)` of Lemma 1 (p. 8) and of the proof of Theorem 1 (p. 9): every edge
`e = uv` of the finite set `C` is cut, and for the choice `s e ∈ Fin 8` (the paper's
`s_e ∈ [8]`, shifted by one) the edge `u → v` is replaced by `u → ▷(O_{s_e})` and
`◁(ρ_{s_e}) → v`.

* Vertices `V′ = V ⊕ (C ⊕ C)`: `inl v` is an original vertex, `inr (inl e)` the new observable
  vertex `▷_e` (tensor (7) of `O_{s_e}`), `inr (inr e)` the new state vertex `◁_e`
  (tensor (5) of `ρ_{s_e}`).
* Edges `E′ = E ⊕ C`: `inl e` is the original edge, which for `e ∈ C` now runs `src e → ▷_e`;
  `inr e` is the new edge `◁_e → tgt e`.
* An original vertex `v` reads the index of `inr e` in place of that of `e` exactly when
  `e ∈ C` and `v = tgt e`; every other vertex keeps reading `inl e`. -/
def cut (G : TensorNetwork) (C : Finset G.E) (s : C → Fin 8) : TensorNetwork where
  V := G.V ⊕ (C ⊕ C)
  E := G.E ⊕ C
  src
    | Sum.inl e => Sum.inl (G.src e)
    | Sum.inr e => Sum.inr (Sum.inr e)
  tgt
    | Sum.inl e => if h : e ∈ C then Sum.inr (Sum.inl ⟨e, h⟩) else Sum.inl (G.tgt e)
    | Sum.inr e => Sum.inl (G.tgt e.1)
  A
    | Sum.inl v => fun α' =>
        G.A v (fun e => if h : e ∈ C ∧ G.tgt e = v then α' (Sum.inr ⟨e, h.1⟩) else α' (Sum.inl e))
    | Sum.inr (Sum.inl e) => fun α' => obsTensor (pauli (s e)) (α' (Sum.inl e.1))
    | Sum.inr (Sum.inr e) => fun α' => stateTensor (eigProj (s e)) (α' (Sum.inr e))

/-- The coefficient of eq. (32): `c_s = Π_{e ∈ C} c_{s_e}`. -/
def coefS {G : TensorNetwork} {C : Finset G.E} (s : C → Fin 8) : ℝ := ∏ e, coef (s e)

end

end ClusterSim.EdgeCut


