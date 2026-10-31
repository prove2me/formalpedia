-- Prove2me | Definitions.Def_CardinalMatching_interpVectors
-- name    : CardinalMatching_interpVectors
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:26:57.064699+00:00
-- url     : https://prove2.me/theorems/f07655af-a864-4d3e-bf27-5b70c8884eb7
-- title:
--   Interpolating agents of the modified instance
-- statement:
--   For two utility vectors $a, b\in\mathbb R^n$, an ordering $\sigma$ of the $n$ types of goods and a step $\varepsilon>0$, the **interpolating chain** from $a$ to $b$ changes coordinate $\sigma(1)$ from $a_{\sigma(1)}$ to $b_{\sigma(1)}$ in steps of size $\varepsilon$ (the last step possibly shorter), then coordinate $\sigma(2)$, and so on. It lists the vector reached after every step, except the final one (which is $b$), and never contains $a$.
--
--   The **interpolating agents** of the modified instance $I'$ are, for every pair $\{i,i'\}$ of distinct original agents, the vectors of the chain between $u_i$ and $u_{i'}$. The order of the types and the direction of the chain are chosen arbitrarily, independently for each pair.
--
--   They connect any two agents by a path of agents whose utilities differ by at most $\varepsilon$ on one type of good, which drives Step 3–4 of the proof of Theorem 8.
--
--   **Formalization Note** A type $t_m$ is the copy class of the $m$-th original good. The order and direction are parameters (`ord`, `rev`), so statements about $I'$ cover every choice. The module also defines `stepCount`, `stepValue` and `interpChain`.
-- source:
--   Tröbst, Vazirani, Cardinal-Utility Matching Markets, arXiv:2402.08851v6, Step 1 item 3 and Figure 1, p.8

import Mathlib

namespace CardinalMatching

/-- Number of `ε`-steps needed to move one coordinate from `a` to `b`: `⌈|b − a| / ε⌉`
(Tröbst–Vazirani, *Cardinal-Utility Matching Markets*, arXiv:2402.08851v6, Step 1 item 3, p.8:
"slowly increasing / decreasing the utility … in steps of ǫ until we reach the utility that i′
has"). -/
noncomputable def stepCount (ε a b : ℝ) : ℕ := ⌈|b - a| / ε⌉₊

/-- The value after `ℓ` steps of size `ε` from `a` towards `b`; the last step (step
`stepCount ε a b`) lands exactly on `b` and may be shorter than `ε`. -/
noncomputable def stepValue (ε a b : ℝ) (ℓ : ℕ) : ℝ :=
  if ℓ < stepCount ε a b then (if a ≤ b then a + ℓ * ε else a - ℓ * ε) else b

/-- **Interpolating chain** from the utility vector `a` to `b` (Tröbst–Vazirani, arXiv:2402.08851v6,
Step 1 item 3 and Figure 1, p.8): with the types ordered `σ 0, σ 1, …, σ (n−1)`, first move the
coordinate `σ 0` from `a (σ 0)` to `b (σ 0)` in steps of `ε` (the last step possibly shorter), then
`σ 1`, and so on. The list holds the utility vector after every step, **except** the final one
(which equals `b`); it never contains the starting vector `a`. So it lists the interpolating
agents strictly between `a` and `b`, the "corner" points included (Figure 1).

**Formalization Note** Utility vectors over the `n` original goods are `Fin n → ℝ`; the type
`σ m` of the paper's ordering `{t₁, …, tₙ}` is the copy class of original good `σ m`. -/
noncomputable def interpChain {n : ℕ} (σ : Equiv.Perm (Fin n)) (ε : ℝ) (a b : Fin n → ℝ) :
    List (Fin n → ℝ) :=
  ((List.finRange n).flatMap fun m =>
    (List.range (stepCount ε (a (σ m)) (b (σ m)))).map fun ℓ =>
      fun t => if σ.symm t < m then b t
        else if σ.symm t = m then stepValue ε (a t) (b t) (ℓ + 1) else a t).dropLast

/-- **All interpolating agents** of the modified instance `I′` (Tröbst–Vazirani,
arXiv:2402.08851v6, Step 1 item 3, p.8): "For each pair {i, i′} of distinct agents in A, we create
a sequence of interpolating agents. Order the types of goods in some arbitrary way {t1, …, tn}.
…" For every pair `i < i'` of original agents, the chain `interpChain (ord i i') ε` from `u_i` to
`u_i'` (or from `u_i'` to `u_i` when `rev i i' = true`), concatenated over all pairs.

**Formalization Note** The paper leaves the order of the types and the direction of each chain
arbitrary; both are parameters (`ord`, `rev`, one choice per pair), so every statement about
`I′` holds for all choices. -/
noncomputable def interpVectors {n : ℕ} (u : Fin n → Fin n → ℝ) (ε : ℝ)
    (ord : Fin n → Fin n → Equiv.Perm (Fin n)) (rev : Fin n → Fin n → Bool) :
    List (Fin n → ℝ) :=
  (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter (fun i' => i < i')).flatMap fun i' =>
      if rev i i' then interpChain (ord i i') ε (u i') (u i)
      else interpChain (ord i i') ε (u i) (u i')

end CardinalMatching


