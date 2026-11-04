-- Prove2me | Definitions.Def_OverbookBL_runState
-- name    : OverbookBL_runState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:53:52.755246+00:00
-- url     : https://prove2.me/theorems/e37f8751-6aa4-49a0-855f-1b522c75a9e8
-- title:
--   Algorithm 1 (online index policy): estimates, admissible selection rules, run, $\mathrm{OBJ}_{\vec A}$
-- statement:
--   Arrival sequences $\vec A=(A_1,\dots,A_T)\in[k]^T$ are i.i.d. with $\mathbb P[A_t=j]=\lambda_j$, so $\vec A$ has probability $\prod_t\lambda_{A_t}$. $N_j[t_1,t_2]$ counts type-$j$ arrivals in periods $t_1,\dots,t_2$.
--
--   The **online index policy** (Algorithm 1) draws a sample $\vec A'$ from the same law and sets $\vec x[0]=0$. In period $t=1,\dots,T$, with arrival of type $j$:
--
--   1. it estimates $\widetilde N^f_{j'}[t]=\#\{\text{type-}j'\text{ arrivals in }\vec A'[t+1,T]\}+\mathbb 1\{j=j'\}$;
--   2. it finds an optimal index solution $\vec x'$ of (1) with inputs $\widetilde N^f[t]$ and $\vec x[t-1]$;
--   3. it accepts the arrival ($x_j[t]=x_j[t-1]+1$) if $x'_j\ge\widetilde N^f_j[t]/2$, and rejects it otherwise.
--
--   A **selection rule** chooses $\vec x'$ from the period, the past and the estimate; it is **admissible** if it always returns an optimal index solution locally optimal at its threshold index. The online objective is $\sum_j v_jx_j[T]-V_B(\vec x[T])$, and $\mathrm{OBJ}_{\vec A}$ is its expectation over $\vec A'$.
--
--   **Formalization Note** Periods are 0-based in Lean. Line 7 is printed with $N^f$; it is read with $\widetilde N^f$, and the box's $\ge$ (the prose under the box says $>$) is used, compared in $\mathbb R$. The algorithm does not say which optimal index solution it finds; the paper assumes only admissibility (p.21), so the rule is a parameter.
-- source:
--   D. Freund and J. Zhao, Overbooking with bounded loss, arXiv:2204.11148v2 (26 Apr 2022), https://arxiv.org/abs/2204.11148v2, Algorithm 1, p.11; p.21

import Definitions.Def_OverbookBL_IsAdmissible

namespace OverbookBL

/-- Probability weight `∏ₜ λ_{Aₜ}` of an arrival sequence `A⃗ = (A₁, …, A_T)` of i.i.d. types
(Freund & Zhao, *Overbooking with bounded loss*, arXiv:2204.11148v2, §2, p.9, "Arrivals").

**Formalization Note** Periods are `Fin T`, 0-based: Lean period `s` is the paper's period
`s + 1`. -/
def seqWeight {k : ℕ} (I : Instance k) {T : ℕ} (A : Fin T → Fin k) : ℝ :=
  ∏ t, I.lam (A t)

/-- `countFrom A t j` is the number of type-`j` arrivals of `A` in the 0-based periods
`s ≥ t`, i.e. `Nⱼ[t+1, T]` in the paper's 1-based notation (arXiv:2204.11148v2, p.9). In
particular `countFrom A 0 j = Nⱼ`. -/
def countFrom {k T : ℕ} (A : Fin T → Fin k) (t : ℕ) (j : Fin k) : ℕ :=
  (Finset.univ.filter (fun s : Fin T => t ≤ s.val ∧ A s = j)).card

/-- The estimate `Ñᶠ[t]` of Algorithm 1, line 5 (arXiv:2204.11148v2, p.11): in (0-based) period
`t`, with current arrival of type `j`, `Ñᶠ_{j'}` is the number of type-`j'` arrivals in the sample
`A⃗′[t+1, T]` (paper's 1-based periods after the current one) plus `𝟙{j = j'}`. -/
def estimate {k T : ℕ} (A' : Fin T → Fin k) (t : ℕ) (j : Fin k) : Fin k → ℕ :=
  fun j' => countFrom A' (t + 1) j' + if j' = j then 1 else 0

/-- A selection rule for line 6 of Algorithm 1 is *admissible* if, for every period, every past
acceptance vector and every estimate, it returns an admissible solution of problem (1): an
optimal index solution that is locally optimal at its threshold index (arXiv:2204.11148v2, p.21).

**Formalization Note** A selection rule is a function `sel t past Nf` of the (0-based) period, the
past acceptance vector `x⃗[t−1]` and the estimate `Ñᶠ[t]`. Algorithm 1 does not say which optimal
index solution line 6 finds; the paper's analysis (p.21) only assumes the property above, so every
such rule is allowed. -/
def IsAdmissibleRule {k : ℕ} (I : Instance k) (B : ℕ)
    (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) : Prop :=
  ∀ (t : ℕ) (past Nf : Fin k → ℕ), IsAdmissible I B past Nf (sel t past Nf)

/-- The state `x⃗[t]` of the online index policy (Algorithm 1, arXiv:2204.11148v2, p.11) after
`t` periods, on the real arrival sequence `A` and the sample `A'`, with selection rule `sel`:
`x⃗[0] = 0` (line 1); in (0-based) period `t` with arrival `j = A t`, compute `Ñᶠ = estimate A' t j`
(line 5) and `x⃗′ = sel t x⃗[t] Ñᶠ` (line 6); accept, i.e. add one to coordinate `j`, iff
`x′ⱼ ≥ Ñᶠⱼ/2` (line 7), otherwise keep the state (lines 8–9).

**Formalization Note** The test of line 7 is printed `x′ⱼ ≥ Nᶠⱼ[t]/2`; it is read with the
estimate `Ñᶠⱼ[t]` (line 6's input; the tilde is missing) and compared in `ℝ`. The prose below the
algorithm says `>`; the algorithm box's `≥` is used, as in the proof of Lemma 3 (p.26). For
`t > T` the state stays `x⃗[T]`. -/
noncomputable def runState {k T : ℕ} (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ))
    (A A' : Fin T → Fin k) : ℕ → (Fin k → ℕ)
  | 0 => 0
  | t + 1 =>
    if h : t < T then
      if ((sel t (runState sel A A' t) (estimate A' t (A ⟨t, h⟩)) (A ⟨t, h⟩) : ℕ) : ℝ) ≥
          ((estimate A' t (A ⟨t, h⟩) (A ⟨t, h⟩) : ℕ) : ℝ) / 2 then
        runState sel A A' t + Pi.single (A ⟨t, h⟩) 1
      else runState sel A A' t
    else runState sel A A' t

/-- Objective `∑ⱼ vⱼ xⱼ[T] − V_B(x⃗[T])` (arXiv:2204.11148v2, p.9) of the online index policy on
the arrival sequence `A` with sample `A'`. -/
noncomputable def onlineObj {k T : ℕ} (I : Instance k) (B : ℕ)
    (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) (A A' : Fin T → Fin k) : ℝ :=
  obj I B 0 (runState sel A A' T)

/-- `OBJ_A⃗`: the expected (over the sample `A⃗′`, drawn i.i.d. with the arrival law in line 2 of
Algorithm 1) objective of the online index policy on the arrival sequence `A⃗`
(arXiv:2204.11148v2, p.11). -/
noncomputable def OBJ {k T : ℕ} (I : Instance k) (B : ℕ)
    (sel : ℕ → (Fin k → ℕ) → (Fin k → ℕ) → (Fin k → ℕ)) (A : Fin T → Fin k) : ℝ :=
  ∑ A' : Fin T → Fin k, seqWeight I A' * onlineObj I B sel A A'

end OverbookBL


