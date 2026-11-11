-- Prove2me | Definitions.Def_FlexRigidity_compExp
-- name    : FlexRigidity_compExp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:18:35.027592+00:00
-- url     : https://prove2.me/theorems/46c251e4-80de-4656-9407-5dde4f26df7f
-- title:
--   The penalized comparison exponent $\mathrm{CompExp}_\alpha(\mathcal G,\mathcal P\circ\mathcal G;S_\Omega)$, eq. (19)
-- statement:
--   For normalized pure inputs $|\sigma^i\rangle_{M_iR_i}$ write $\sigma^{i,\mathcal G_i}=(\mathcal G_i\otimes\mathrm{id}_{R_i})[|\sigma^i\rangle\langle\sigma^i|]$ and $\sigma^{i,\mathcal P_i\circ\mathcal G_i}$ likewise, let $P_{C_i}$ be their common distribution on $C_i$, and let $\cdot_{|c}$ denote the normalized conditional state on the block $C_i=c$. Then
--   $$\mathrm{CompExp}_\alpha(\mathcal G,\mathcal P\circ\mathcal G;S_\Omega)=\sup_{\substack{|\sigma^1\rangle,\dots,|\sigma^n\rangle\\ Q_{C_1},\dots,Q_{C_n}:\ \frac1n\sum_iQ_{C_i}\in S_\Omega}}\ \sum_{i=1}^n\Big[\sum_cQ_{C_i}(c)D_\alpha\big(\sigma^{i,\mathcal G_i}_{|c}\big\|\sigma^{i,\mathcal P_i\circ\mathcal G_i}_{|c}\big)-\frac{D(Q_{C_i}\|P_{C_i})}{\alpha-1}\Big],$$
--   where a term with $Q_{C_i}(c)=0$ is zero and a term with $P_{C_i}(c)=0<Q_{C_i}(c)$ is $-\infty$.
--
--   **Formalization Note** The reference is $R_i\cong M_i$. The KL term is distributed over $c$, which reproduces the printed conventions. Values in $\overline{\mathbb R}$; under Postulate Set 4.1 every $D_\alpha$ here is finite, so no $(+\infty)+(-\infty)$ arises.
-- source:
--   Arqand, Kundu, Tan, Flexible rigidity: Compiling generic trusted-preparation protocols into sequential device-independent protocols, arXiv:2610.00444 (artifact sha256 8c67699d…), eq. (19), p. 29

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P35
import Definitions.Def_FlexRigidity_SeqData
import Definitions.Def_FlexRigidity_blockC
import Definitions.Def_DHRUniq_IsUnitVec
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_FlexRigidity_IsDistribution
set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Filter Topology
open QAlgorithms (Superop IsChannel krausApply idTensorSuperop piSuperop)
open QAlgorithms.Papers.Independent.Dependency50.P35 (tr Density Dominates divergence rawTrace spectralPower maxRelative POVM leftMarginal rightMarginal)

noncomputable section

namespace FlexRigidity

/-- **The penalized comparison exponent, eq. (19)** (Arqand–Kundu–Tan, *Flexible rigidity*,
arXiv:2610.00444, artifact sha256 8c67699d…, p. 29):
`CompExp_α(G, P∘G; S_Ω) = sup Σ_{i=1}^n [ Σ_c Q_{C_i}(c) D_α(σ^{i,G_i}_{|c} ‖ σ^{i,P_i∘G_i}_{|c}) − D(Q_{C_i}‖P_{C_i})/(α−1) ]`,
the supremum over normalized pure inputs `|σ^i⟩_{M_i R_i}` and distributions `Q_{C_1}, …, Q_{C_n}`
on `C` with `(1/n) Σ_i Q_{C_i} ∈ S_Ω`. Here `σ^{i,G_i} = (G_i ⊗ id_{R_i})[|σ^i⟩⟨σ^i|]`,
`σ^{i,P_i∘G_i}` likewise, `P_{C_i}` is their common distribution on `C_i`, and `·_{|c}` is the
normalized conditional state. A term with `Q_{C_i}(c) = 0` is zero; a term with
`P_{C_i}(c) = 0 < Q_{C_i}(c)` is `−∞`.

**Formalization Note** The reference is `R_i ≅ M_i` (the type `M i`, placed first). The KL term is
distributed over `c`: the `c`-term is `Q(c) D_α(·|c) − Q(c) log(Q(c)/P(c))/(α−1)`, log base 2,
which has the printed conventions. Values in `EReal`. Under Postulate Set 4.1 every `D_α` here is
finite (positive definite replacement), so no `⊤ + ⊥` arises. -/
def compExp {C : Type} {O M Z S J : ℕ → Type} [Fintype C] [DecidableEq C]
    [∀ k, Fintype (M k)] [∀ k, DecidableEq (M k)] [∀ k, Fintype (Z k)] [∀ k, DecidableEq (Z k)]
    [∀ k, Fintype (S k)] [∀ k, DecidableEq (S k)] [∀ k, Fintype (J k)] [∀ k, DecidableEq (J k)]
    (D : SeqData C O M Z S J) (n : ℕ) (a : ℝ) (SΩ : Set (C → ℝ)) : EReal :=
  sSup {v : EReal | ∃ (σ : (i : Fin n) → (M i × M i → ℂ)) (Q : Fin n → C → ℝ),
    (∀ i, DHRUniq.IsUnitVec (σ i)) ∧ (∀ i, IsDistribution (Q i)) ∧
    (fun c => (1 / (n : ℝ)) * ∑ i, Q i c) ∈ SΩ ∧
    v = ∑ i : Fin n, ∑ c : C,
      (let σG := idTensorSuperop (R := M i) (D.G i) (ObliviousRSP.pureState (σ i))
       let σPG := idTensorSuperop (R := M i) (fun X => D.P i (D.G i X)) (ObliviousRSP.pureState (σ i))
       let p := tr (blockC (D.cOf i) c σG)
       if Q i c = 0 then (0 : EReal)
       else if p = 0 then ⊥
       else (Q i c : EReal) * divergence a (((p⁻¹ : ℝ) : ℂ) • blockC (D.cOf i) c σG)
              (((p⁻¹ : ℝ) : ℂ) • blockC (D.cOf i) c σPG)
            - ((Q i c * Real.logb 2 (Q i c / p) / (a - 1) : ℝ) : EReal))}

end FlexRigidity


