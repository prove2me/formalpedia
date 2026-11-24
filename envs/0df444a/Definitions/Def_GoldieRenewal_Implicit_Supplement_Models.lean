-- Prove2me | Definitions.Def_GoldieRenewal_Implicit_Supplement_Models
-- name    : GoldieRenewal_Implicit_Supplement_Models
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T01:12:22.617261+00:00
-- url     : https://prove2.me/theorems/65fefc0e-fefb-48b2-8f0b-135f81160571
-- title:
--   Random equations (1.2), (1.3), (8.1) as law operators; R̃ = ⋁ Q_kΠ_{k−1} (Prop. 5.1); Ξ_n and the law in (8.3) (Prop. 8.1)
-- statement:
--   Objects of the random equations of §§5, 6 and 8. In each equation the unknown is independent of the coefficients, and $\overset{L}{=}$ denotes equality of laws.
--
--   1. **Equation (1.2)**, $R\overset{L}{=}\max(Q,MR)$, $R$ independent of $(M,Q)$. For the joint law $\mu$ of $(Q,M)$ and a law $\rho$ on $\mathbb R$, the operator $T_\mu\rho$ is the law of $\max(Q,MR)$ when $R\sim\rho$ is independent of $(Q,M)$. A law for $R$ satisfying (1.2) is a probability law with $T_\mu\rho=\rho$.
--   2. **Equation (1.3)**, $R\overset{L}{=}Q+M\max(L,R)$, $R$ independent of $(L,M,Q)$ (Letac's model E). For the joint law of $(Q,M,L)$, the operator returns the law of $Q+M\max(L,R)$.
--   3. **Equation (8.1)**, $S\overset{L}{=}MS+N\sqrt S+Q$, $S$ independent of $(Q,N,M)$. For the joint law of $(Q,N,M)$ and a law $\rho$ on $[0,\infty)$, the operator returns the law of $MS+N\sqrt S+Q$ for $S\sim\rho$.
--   4. **The supremum of Proposition 5.1.** For i.i.d. pairs $(Q_k,M_k)$, $k\ge1$, and $\Pi_k:=M_1\cdots M_k$ ($\Pi_0=1$),
--   $$
--   \tilde R := \bigvee_{k=1}^\infty Q_k\Pi_{k-1}.
--   $$
--   5. **The maps of Proposition 8.1.** For i.i.d. triples $(Q_n,N_n,M_n)$, $\Xi_n(t):=M_nt+N_n\sqrt t+Q_n$, $t\ge0$.
--   6. **The law in (8.3).** The law of $M+N/(2\sqrt{Q'})$, where $(Q,N,M)$ has the given joint law and $Q'$ is an independent copy of $Q$.
--
--   These give the "unique law" statements of Propositions 5.1, 8.1 and Theorems 5.2, 6.2, 8.2 a precise meaning, and the hypothesis "$R$ solves (·)" of the rate theorems.
--
--   **Formalization Note** Each operator is the image of $\mu\otimes\rho$ under the right-hand side of the equation, so independence of the unknown from the coefficients is built in. Coordinates: $(Q,M)$ for (1.2); $(Q,M,L)$ for (1.3); $(Q,N,M)$ for (8.1). $\tilde R$ is a real supremum, which Lean sets to $0$ for a sequence unbounded above; every statement using it also asserts a.s. boundedness. $\sqrt s$ is Lean's `Real.sqrt`, $0$ for $s<0$; the operator of (8.1) is only applied to laws on $[0,\infty)$. The division in (8.3) is only used when $Q>0$ a.s. Sequences are stored 0-based.
-- source:
--   Goldie, Implicit renewal theory and tails of solutions of random equations, Ann. Appl. Probab. 1(1):126–166 (1991), DOI 10.1214/aoap/1177005985, p. 126, (1.1)–(1.3); p. 138, §5 and Proposition 5.1; p. 139, (6.1); p. 142, (8.1)–(8.3) and Proposition 8.1

import Mathlib

namespace GoldieRenewal.Implicit.Supplement

open MeasureTheory

/-! Law-level operators of the random equations (1.2), (1.3) and (8.1) (Goldie 1991, pp. 126,
142), and the objects of Propositions 5.1 and 8.1 (pp. 138, 142).

For a joint law `μ` of the coefficients and a law `ρ` on `ℝ`, the operator returns the law of the
right-hand side when the unknown has law `ρ` and is independent of the coefficients: the image of
`μ ⊗ ρ`. A law "for `R` satisfying (·)" is a probability measure fixed by the operator. -/

/-- **Equation (1.2)** `R =_L max(Q, MR)`, `R` independent of `(M, Q)` (Goldie 1991, p. 126; §5,
p. 138). `μ` is the joint law of `(Q, M)` (first coordinate `Q`, second `M`, as in
`GoldieRenewal.Kesten.rdeOperator`); the result is the law of `max(Q, MR)` for `R ∼ ρ`
independent of `(Q, M)`. -/
noncomputable def extremalOperator (μ : Measure (ℝ × ℝ)) (ρ : Measure ℝ) : Measure ℝ :=
  (μ.prod ρ).map (fun p : (ℝ × ℝ) × ℝ => max p.1.1 (p.1.2 * p.2))

/-- **Equation (1.3)** `R =_L Q + M max(L, R)`, `R` independent of `(L, M, Q)` (Goldie 1991,
p. 126; Letac's model E, (6.1), p. 139). `μ` is the joint law of `(Q, M, L)`: `p.1 = Q`,
`p.2.1 = M`, `p.2.2 = L`. -/
noncomputable def letacEOperator (μ : Measure (ℝ × ℝ × ℝ)) (ρ : Measure ℝ) : Measure ℝ :=
  (μ.prod ρ).map (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.1 + p.1.2.1 * max p.1.2.2 p.2)

/-- **Equation (8.1)** `S =_L MS + N√S + Q`, `S` independent of `(Q, N, M)` (Goldie 1991, p. 142).
`μ` is the joint law of `(Q, N, M)`: `p.1 = Q`, `p.2.1 = N`, `p.2.2 = M`.

**Formalization Note** `Real.sqrt` is `0` on negative reals; the operator is only applied to laws
`ρ` on `[0, ∞)` (`ρ (Set.Iio 0) = 0`), where `√s` is the paper's square root. -/
noncomputable def polyOperator (μ : Measure (ℝ × ℝ × ℝ)) (ρ : Measure ℝ) : Measure ℝ :=
  (μ.prod ρ).map (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2 * p.2 + p.1.2.1 * Real.sqrt p.2 + p.1.1)

/-- The terms `Q_k Π_{k−1}`, `k = 1, 2, …`, of `R̃ := ⋁_{k=1}^∞ Q_k Π_{k−1}` (Goldie 1991,
Proposition 5.1, p. 138), where `Π_k := M₁ ⋯ M_k`, `Π₀ = 1`. The sequence `(Q_k, M_k)` is stored
0-based: `QM i = (Q_{i+1}, M_{i+1})`, so the `i`-th term is `Q_{i+1} · M₁ ⋯ M_i`. -/
def extremalTerm {Ω : Type*} (QM : ℕ → Ω → ℝ × ℝ) (i : ℕ) (ω : Ω) : ℝ :=
  (QM i ω).1 * ∏ j ∈ Finset.range i, (QM j ω).2

/-- `R̃ := ⋁_{k=1}^∞ Q_k Π_{k−1}` (Goldie 1991, Proposition 5.1, p. 138), as a real supremum.

**Formalization Note** A real `⨆` is `0` for a sequence unbounded above; every statement using
`extremalSup` also asserts that the sequence is a.s. bounded above, so on that event this is the
paper's (finite) `R̃`. The supremum is never `−∞`: the first term `Q₁` is real. -/
noncomputable def extremalSup {Ω : Type*} (QM : ℕ → Ω → ℝ × ℝ) (ω : Ω) : ℝ :=
  ⨆ i : ℕ, extremalTerm QM i ω

/-- The random map `Ξ_n(t) := M_n t + N_n √t + Q_n`, `t ≥ 0` (Goldie 1991, Proposition 8.1,
p. 142). The sequence `(Q_n, N_n, M_n)` is stored 0-based: `QNM i = (Q_{i+1}, N_{i+1}, M_{i+1})`,
and `xiMap QNM i` is the paper's `Ξ_{i+1}`.

**Formalization Note** The paper defines `Ξ_n` on `[0, ∞)`; for nonnegative coefficients it maps
`[0, ∞)` into itself, and the statements only evaluate it there. -/
noncomputable def xiMap {Ω : Type*} (QNM : ℕ → Ω → ℝ × ℝ × ℝ) (i : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  (QNM i ω).2.2 * t + (QNM i ω).2.1 * Real.sqrt t + (QNM i ω).1

/-- The law of `M + N/(2√Q′)` in (8.3) (Goldie 1991, p. 142), where `(Q, N, M)` has joint law `μ`
and `Q′` is an independent copy of `Q`: the image of `μ ⊗ μ_Q` under
`((q, n, m), q′) ↦ m + n/(2√q′)`.

**Formalization Note** It is only used when `Q > 0` a.s., so `√q′ > 0` off a null set and the
division is the paper's. -/
noncomputable def coeffLaw83 (μ : Measure (ℝ × ℝ × ℝ)) : Measure ℝ :=
  (μ.prod (μ.map Prod.fst)).map
    (fun p : (ℝ × ℝ × ℝ) × ℝ => p.1.2.2 + p.1.2.1 / (2 * Real.sqrt p.2))

end GoldieRenewal.Implicit.Supplement


