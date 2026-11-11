-- Prove2me | Definitions.Def_FlowSparsSchur_Main_Embedding
-- name    : FlowSparsSchur_Main_Embedding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T01:23:47.726372+00:00
-- url     : https://prove2.me/theorems/43abda8e-9b48-4e78-a803-8ac8448aa246
-- title:
--   Electrical embeddings, dominating capacities, reverse congestion, the normalized maps Π, and the spectral norm
-- statement:
--   Let $G$ be a graph on $V$ with conductances and capacities, and $H$ a graph with conductances on a terminal set $S\subseteq V$. The **forward electrical embedding** of $G$ into $H$ and the **dominating capacities** (Definition 5.1) are
--   $$E_{G\to H}=C_HB_HL_H^\dagger P_{G\to V(H)}B_G^\top U_G,\qquad \nu(G\to H)=\overline{E}_{G\to H}\mathbf 1,$$
--   where $\overline M$ is the entrywise absolute value; $H_\nu$ is $H$ with capacities $\nu$. The **reverse electrical embedding** and its **congestion** are
--   $$E_{H\to G}=C_GB_GL_G^\dagger P_{H\to V(G)}B_H^\top U_H,\qquad \mathrm{cong}_{H\to G}=U_G^{-1}\overline{E}_{H\to G}\mathbf 1 ,$$
--   and for any matrix $E\in\mathbb R^{E(G)\times E(H)}$, $\mathrm{cong}(E)=U_G^{-1}\overline{E}\mathbf 1$.
--
--   The **normalized maps** of Theorem 9.1, with $H=\mathrm{Schur}(G,S)$ and $\widetilde H$ a graph on $S$, are
--   $$\Pi_{G\to\widetilde H}=D_{\widetilde H}L_{\widetilde H}^\dagger P_{G\to S}D_G^\top,\qquad \Pi_{\widetilde H\to G}=D_GP_{G\to S}^\top L_H^\dagger D_{\widetilde H}^\top ,$$
--   and §7 (p. 25) uses $\Pi^{(7)}_{\widetilde H\to G}=C_G^{1/2}B_GL_G^\dagger P_{\widetilde H\to V(G)}B_{\widetilde H}^\top C_{\widetilde H}^{1/2}$. $\|x\|_2$ is the Euclidean norm, and $\|A\|_2\le c$ (spectral norm) means $\|Ax\|_2\le c\|x\|_2$ for every $x$. For a graph $G$ and $x\in\mathbb R^{E(G)}$, $\tfrac12\sum_{e\ni v}x(e)^2$ is the half endpoint mass at $v$ (the vectors $\alpha,\nu$ of Lemma 9.44).
--
--   **Formalization Note** The capacities of $H$ are not used by `fwdEmb`; `revEmb` uses those of $H$ (in the paper they are $\nu$). `OpNormLe A c` encodes $\|A\|_2\le c$ without a supremum.
-- source:
--   Goranci, Henzinger, Momeni, Räcke, Sricharan, Breaking the Quadratic Time Barrier for Flow Sparsifiers via Schur Complement Localization, STOC 2027 submission (manuscript of November 3, 2026, sha256 0e498585…3266), pp. 17–18, §5 and Definition 5.1; p. 25, §7; p. 28, Theorem 9.1; p. 48, Lemma 9.44

import Mathlib
import Definitions.Def_FlowSparsSchur_Main_Graph

/-!
# Electrical embeddings, dominating capacities, reverse congestion and the normalized maps Π

Goranci, Henzinger, Momeni, Räcke, Sricharan, *Breaking the Quadratic Time Barrier for Flow
Sparsifiers via Schur Complement Localization*, STOC 2027 submission, §5 (pp. 16–18, Definition
5.1), §7 (p. 25, the characterization), Theorem 9.1 and Definition 9.18 (pp. 28, 33).

`G` is a graph on `V` (edges `E`), `H` a graph on the terminal set `S ⊆ V` (edges `F`).
* `E_{G→H} = C_H B_H L_H^† P_{G→V(H)} B_Gᵀ U_G` (forward electrical embedding);
  `ν(G→H) = Ē_{G→H} 1` (dominating capacities, Definition 5.1).
* `E_{H→G} = C_G B_G L_G^† P_{H→V(G)} B_Hᵀ U_H` (reverse electrical embedding);
  `cong_{H→G} = U_G⁻¹ Ē_{H→G} 1`.
* §9: `Π_{G→H̃} = D_H̃ L_H̃^† P_{G→S} D_Gᵀ`, `Π_{H̃→G} = D_G P_{G→S}ᵀ L_H^† D_H̃ᵀ` with
  `H = Schur(G, S)`.
* §7: `Π_{H̃→G} = C_G^{1/2} B_G L_G^† P_{H̃→V(G)} B_H̃ᵀ C_H̃^{1/2}`.
* `‖A‖₂ ≤ c` (spectral norm): `‖A x‖₂ ≤ c ‖x‖₂` for every `x`.
* `halfEndpointMass G x v = ½ Σ_{e ∋ v} x(e)²` (the vectors `α`, `ν` of Lemma 9.44).
-/

namespace FlowSparsSchur.Main

open Matrix

variable {V E F : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] [Fintype F]
  [DecidableEq F]

/-- Forward electrical embedding `E_{G→H} = C_H B_H L_H^† P_{G→V(H)} B_Gᵀ U_G ∈ ℝ^{E(H) × E(G)}`
(§5; the capacities of `H` are not used). -/
noncomputable def fwdEmb (S : Finset V) (G : CGraph V E) (H : CGraph S F) : Matrix F E ℝ :=
  H.condMat * H.incidence * pinv H.lap * schurProj G S * (G.incidence)ᵀ * G.capMat

/-- Dominating capacities `ν(G → H) = Ē_{G→H} 1 ∈ ℝ^{E(H)}` (Definition 5.1). -/
noncomputable def domCap (S : Finset V) (G : CGraph V E) (H : CGraph S F) : F → ℝ :=
  fun f => ∑ e, |fwdEmb S G H f e|

/-- Reverse electrical embedding `E_{H→G} = C_G B_G L_G^† P_{H→V(G)} B_Hᵀ U_H ∈ ℝ^{E(G) × E(H)}`
(§5). -/
noncomputable def revEmb (S : Finset V) (G : CGraph V E) (H : CGraph S F) : Matrix E F ℝ :=
  G.condMat * G.incidence * pinv G.lap * padOf S * (H.incidence)ᵀ * H.capMat

/-- The congestion `U_G⁻¹ Ē 1 ∈ ℝ^{E(G)}` on `E(G)` of an embedding matrix `Emb ∈ ℝ^{E(G) × E(H)}`. -/
noncomputable def congOf (G : CGraph V E) (Emb : Matrix E F ℝ) : E → ℝ :=
  fun e => (∑ f, |Emb e f|) / G.cap e

/-- `cong_{H→G} = U_G⁻¹ Ē_{H→G} 1` (§5). -/
noncomputable def revCong (S : Finset V) (G : CGraph V E) (H : CGraph S F) : E → ℝ :=
  congOf G (revEmb S G H)

/-- `Π_{G→H̃} = D_H̃ L_H̃^† P_{G→S} D_Gᵀ ∈ ℝ^{E(H̃) × E(G)}` (Theorem 9.1). -/
noncomputable def piFwd (S : Finset V) (G : CGraph V E) (Ht : CGraph S F) : Matrix F E ℝ :=
  Ht.wInc * pinv Ht.lap * schurProj G S * (G.wInc)ᵀ

/-- `Π_{H̃→G} = D_G P_{G→S}ᵀ L_H^† D_H̃ᵀ ∈ ℝ^{E(G) × E(H̃)}` with `L_H = L_{Schur(G,S)}`
(Theorem 9.1). -/
noncomputable def piRev (S : Finset V) (G : CGraph V E) (Ht : CGraph S F) : Matrix E F ℝ :=
  G.wInc * (schurProj G S)ᵀ * pinv (schurLap G S) * (Ht.wInc)ᵀ

/-- §7's `Π_{H̃→G} = C_G^{1/2} B_G L_G^† P_{H̃→V(G)} B_H̃ᵀ C_H̃^{1/2} ∈ ℝ^{E(G) × E(H̃)}` (p. 25). -/
noncomputable def piRevSec7 (S : Finset V) (G : CGraph V E) (Ht : CGraph S F) : Matrix E F ℝ :=
  G.sqrtCondMat * G.incidence * pinv G.lap * padOf S * (Ht.incidence)ᵀ * Ht.sqrtCondMat

/-- Euclidean norm `‖x‖₂` of a real vector. -/
noncomputable def norm2 {n : Type} [Fintype n] (x : n → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- `‖A‖₂ ≤ c` for the spectral (operator `2`-) norm: `‖A x‖₂ ≤ c ‖x‖₂` for every `x`. -/
def OpNormLe {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℝ) (c : ℝ) : Prop :=
  ∀ x : n → ℝ, norm2 (A *ᵥ x) ≤ c * norm2 x

/-- Half the squared weight at the endpoints: `α(v) = ½ Σ_{e ∈ E, v ∈ e} x(e)²` (Lemma 9.44). -/
noncomputable def halfEndpointMass {W : Type} [DecidableEq W] (G : CGraph W E) (x : E → ℝ) (v : W) : ℝ :=
  (1 / 2) * ∑ e, if G.src e = v ∨ G.dst e = v then x e ^ 2 else 0

end FlowSparsSchur.Main


