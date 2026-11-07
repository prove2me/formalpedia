-- Prove2me | Definitions.Def_ChoresEFX_Alg1Run
-- name    : ChoresEFX_Alg1Run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:12:17.636891+00:00
-- url     : https://prove2.me/theorems/cae1ee2f-cd64-4ec9-8317-2ff3d7dbbc9f
-- title:
--   Working costs, the general pipeline and the run relation of Algorithm 1
-- statement:
--   The **working costs** of an instance are $\hat C=c$ if all costs are positive, and otherwise $\hat C_i(g)=D_ic_i(g)+\varepsilon/(32m)$, where $D_i$ is the least common multiple of the denominators of row $i$.
--
--   The **general pipeline** with parameter $k$ runs MFCP with $\beta_k(t)$, then SSR, then the packet decomposition, then APR with factor $\lambda$.
--
--   A **run of Algorithm 1** on $(I,\varepsilon)$ with output $\sigma$ falls into one of three cases: $n=1$; or $m\le2n$ and $X=\sigma^{-1}$ is an output of BRBI with $k=1$ on the original costs; or $m>2n$ and $X=\sigma^{-1}$ is an output of the general pipeline on $\hat C$ with $k=1$, $t=\varepsilon/100$ and $\lambda_0=3+\varepsilon/4$.
--
--   This relation names the algorithm whose correctness the mission states.
--
--   **Formalization Note** The printed pseudocode has no line for $n=1$. The overview (p.3) says the algorithm "handles the single-agent case directly", and the proof treats it first (p.19).
-- source:
--   Qin, Fang, Li, Liu, Chen, Polynomial-Time Approximate EFX for Chores via Flow and Matching, STOC 2027 submission (manuscript sha256 b26d14cf…), §3 p.6; Algorithm 1, p.7; §1.2 p.3; proof of Theorem 1.1, p.19

import Mathlib
import Definitions.Def_ChoresEFX_Inst
import Definitions.Def_ChoresEFX_IsMfcpOutput
import Definitions.Def_ChoresEFX_IsAdmissibleMatching
import Definitions.Def_ChoresEFX_AprRun
import Definitions.Def_ChoresEFX_BrbiRun

namespace ChoresEFX

open Finset

/-- The scaling factor `D_i = lcm_g d_ig` of row `i`, §3, p.6.

Qin, Fang, Li, Liu, Chen, *Polynomial-Time Approximate EFX for Chores via Flow and Matching*, STOC 2027
submission (manuscript sha256 b26d14cf…). Lean's rationals are already in lowest terms, and `0 = 0/1`,
as the page requires. -/
def rowDen (I : Inst) (i : Fin I.n) : ℕ := (univ : Finset (Fin I.m)).lcm fun g => (I.c i g).den

open Classical in
/-- **The working costs**, Algorithm 1, lines 4–9, p.7 (Qin et al., STOC 2027 submission): `Ĉ = c` if
all costs are positive, otherwise `Ĉ_i(g) = D_i c_i(g) + ε/(32m)`. -/
noncomputable def workingCost (I : Inst) (ε : ℚ) : Fin I.n → Fin I.m → ℝ :=
  if ∀ i g, 0 < I.c i g then I.realCost
  else fun i g => (rowDen I i : ℝ) * (I.c i g : ℝ) + (ε : ℝ) / (32 * (I.m : ℝ))

/-- **The general pipeline**, Algorithm 1, lines 11–16, p.7, and the "EFkX Extension", p.13 (Qin et al.,
STOC 2027 submission), with output `X`: MFCP with `β = β_k(t)`, SSR, packet decomposition, and APR with
`ρ = ρ_k(t)` and factor `lam`. Every choice of each stage is free. -/
def GeneralRun {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : ι → κ → ℝ) (k : ℕ) (t lam : ℝ) (X : ι → Finset κ) : Prop :=
  ∃ (p : κ → ℝ) (γ : ι → ℝ) (w : ι → κ → ℝ) (o : ι → κ → ℕ)
    (π : κ → Σ i, Fin (numSlots w i)) (S : ι → Finset κ) (K : ι → List (Finset κ)),
    IsMfcpOutput C t (betaParam k t) p γ w ∧
    IsSortedOrder (betaParam k t) p o ∧ IsAdmissibleMatching w o π ∧
    (∀ i, IsAgentPacketDecomp k (betaParam k t) (rhoParam k t) p (ssrBundle π i) (S i) (K i)) ∧
    AprRun C k lam S K X

/-- **A run of Algorithm 1**, p.7 (Qin et al., STOC 2027 submission), with output `σ`: the single agent
takes everything; if `m ≤ 2n`, BRBI with `k = 1`; otherwise the general pipeline on the working costs with
`t = ε/100` and `λ₀ = 3 + ε/4`.

**Formalization Note.** The printed pseudocode has no line for `n = 1`; §1.2, p.3 says the algorithm
"handles the single-agent case directly", and the proof says "The case n = 1 is immediate" (p.19). For
`n = 1` there is only one `σ`. -/
def Alg1Run (I : Inst) (ε : ℚ) (σ : Fin I.m → Fin I.n) : Prop :=
  I.n = 1 ∨
    (I.n ≠ 1 ∧ I.m ≤ 2 * I.n ∧ BrbiRun I.realCost 1 (bundle σ)) ∨
    (I.n ≠ 1 ∧ 2 * I.n < I.m ∧
      GeneralRun (workingCost I ε) 1 ((ε : ℝ) / 100) (3 + (ε : ℝ) / 4) (bundle σ))

end ChoresEFX


