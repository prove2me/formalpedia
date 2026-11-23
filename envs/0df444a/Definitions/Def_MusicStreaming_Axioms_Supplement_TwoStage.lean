-- Prove2me | Definitions.Def_MusicStreaming_Axioms_Supplement_TwoStage
-- name    : MusicStreaming_Axioms_Supplement_TwoStage
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:25:47.737743+00:00
-- url     : https://prove2.me/theorems/324d37bb-8f7a-4fef-a408-502eef182048
-- title:
--   §5, p. 16 — the two-stage rule R^{ψ,φ} of two bankruptcy rules
-- statement:
--   Let $\psi$ and $\varphi$ be two bankruptcy rules. The **two-stage rule** $R^{\psi,\varphi}$ is the claims rule obtained as follows from a claims problem $(N,K,c,E)$.
--
--   1. *First stage.* Divide $E$ among the issues by solving the bankruptcy problem $(K,c^K,E)$ with $c^K_j=\sum_{i\in N}c_{ij}$, giving $\psi_j(K,c^K,E)$ for each $j\in K$.
--   2. *Second stage.* For each issue $j\in K$, divide its award among the agents by solving the bankruptcy problem $(N,c_{\cdot j},\psi_j(K,c^K,E))$ with $\varphi$.
--
--   The agent's final amount is the sum over the issues:
--
--   $$R^{\psi,\varphi}_i(N,K,c,E)=\sum_{j\in K}\varphi_i\big(N,c_{\cdot j},\psi_j(K,c^K,E)\big).$$
--
--   The rules $R^{P,P}$ and $R^{CEA,P}$ are the two-stage rules compared with the pro-rata and user-centric indices in Theorem 4(b)–(c).
--
--   **Formalization Note** The source prints $c^K_j=\sum_{i\in N}c_{ji}$ and writes the second-stage problem as $(N,\psi_j(K,E,c^K),c_{\cdot j})$; the dimensions, the final display of p. 16 and every computation on pp. 26–27 fix the reading used here, $c^K_j=\sum_{i\in N}c_{ij}$ and $\varphi_i(N,c_{\cdot j},\psi_j(K,c^K,E))$. The composition is defined for arbitrary rules $\psi,\varphi$ and is not replaced by any closed form.
-- source:
--   Bergantiños, Moreno-Ternero, Revenue sharing at music streaming platforms, arXiv:2310.11861v1, p. 16, §5 (two-stage rule, items 1–2 and display)

import Mathlib
import Definitions.Def_MusicStreaming_Axioms_Supplement_Bankruptcy
import Definitions.Def_MusicStreaming_Axioms_Supplement_Claims

namespace MusicStreaming.Axioms.Supplement

variable {α κ : Type*}

/-- The first-stage bankruptcy problem among the issues (p. 16): `(K, c^K, E)` with
`c^K_j = ∑_{i ∈ N} c_ij`. -/
def ClaimsProblem.issueProblem (P : ClaimsProblem α κ) : BankruptcyProblem κ :=
  ⟨P.K, P.issueTotal, P.E⟩

/-- The second-stage bankruptcy problem of issue `j` (p. 16): the agents `N`, the claims
`c_{·j} = (c_ij)_{i ∈ N}` and the amount `a` that the first stage assigned to issue `j`. -/
def ClaimsProblem.secondStage (P : ClaimsProblem α κ) (j : κ) (a : ℝ) : BankruptcyProblem α :=
  ⟨P.N, fun i => P.c i j, a⟩

/-- The two-stage rule `R^{ψ,φ}` of two bankruptcy rules `ψ` (first stage, among issues) and
`φ` (second stage, among agents) (p. 16):
`R^{ψ,φ}_i(N, K, c, E) = ∑_{j ∈ K} φ_i(N, c_{·j}, ψ_j(K, c^K, E))`. -/
noncomputable def twoStage (ψ : BankruptcyRule κ) (φ : BankruptcyRule α) : ClaimsRule α κ :=
  fun P i => ∑ j ∈ P.K, φ (P.secondStage j (ψ P.issueProblem j)) i

end MusicStreaming.Axioms.Supplement


