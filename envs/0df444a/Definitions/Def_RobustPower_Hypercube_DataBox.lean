-- Prove2me | Definitions.Def_RobustPower_Hypercube_DataBox
-- name    : RobustPower_Hypercube_DataBox
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T07:48:36.727978+00:00
-- url     : https://prove2.me/theorems/7eb36688-34d6-47f9-a174-db9d31710049
-- title:
--   The joint uncertainty set $\mathcal U=\{(A(\omega),B(\omega),b(\omega),d(\omega))\}$ and hypercubes (Definition 1.1)
-- statement:
--   In §5.3 every piece of second-stage data is uncertain. A **scenario datum** is a quadruple $(A,B,b,d)$ with $A\in\mathbb R^{m\times n_1}$, $B\in\mathbb R^{m\times n_2}$, $b\in\mathbb R^m$ and $d\in\mathbb R^{n_2}$; listing all entries, it is a point $\mathrm{vec}(A,B,b,d)$ of $\mathbb R^N$ with $N=mn_1+mn_2+m+n_2$.
--
--   Order scenario data **entrywise**: $s\le t$ when every entry of $s$ is at most the corresponding entry of $t$. For $l\le u$ the **box** is
--
--   $$[l,u]=\{s : l\le s\le u\}=[l_1,u_1]\times\cdots\times[l_N,u_N].$$
--
--   Following Definition 1.1, a set $\mathcal U$ of scenario data is a **hypercube** if $\mathcal U=[l,u]$ for some $l\le u$.
--
--   Given a scenario set $\Omega$ and maps $\omega\mapsto A(\omega),B(\omega),b(\omega),d(\omega)$, the **uncertainty set** is the set of realized data
--
--   $$\mathcal U=\{(A(\omega),B(\omega),b(\omega),d(\omega)) : \omega\in\Omega\}.$$
--
--   "The uncertainty set is a hypercube" therefore says that the realized data are exactly a full box: every corner and every interior point of the box is realized by some scenario.
--
--   **Formalization Note** A scenario datum is a Lean structure with four fields; the order and the box are written out entrywise on the four blocks, which is the componentwise order of $\mathbb R^N$.
-- source:
--   Bertsimas & Goyal, On the Power of Robust Solutions in Two-Stage Stochastic and Adaptive Optimization Problems, authors' manuscript (MIT DSpace) of Math. Oper. Res. DOI 10.1287/moor.1090.0440, p. 5, Definition 1.1; p. 31, definition of U and Theorem 5.4

import Mathlib

namespace RobustPower.Hypercube

/-- One realization `(A, B, b, d)` of all the uncertain data of (5.6)–(5.7):
`A ∈ ℝ^{m×n₁}`, `B ∈ ℝ^{m×n₂}`, `b ∈ ℝ^m`, `d ∈ ℝ^{n₂}`. As a point of `ℝ^N`,
`N = m n₁ + m n₂ + m + n₂`, it is the vector `vec(A, B, b, d)` of p. 32. -/
structure ScenarioData (m n₁ n₂ : ℕ) where
  A : Matrix (Fin m) (Fin n₁) ℝ
  B : Matrix (Fin m) (Fin n₂) ℝ
  b : Fin m → ℝ
  d : Fin n₂ → ℝ

/-- The componentwise order on `ℝ^N`, read on the four blocks: every entry of
`s` is at most the corresponding entry of `t`. -/
def DataLE {m n₁ n₂ : ℕ} (s t : ScenarioData m n₁ n₂) : Prop :=
  (∀ i j, s.A i j ≤ t.A i j) ∧ (∀ i j, s.B i j ≤ t.B i j) ∧
    (∀ i, s.b i ≤ t.b i) ∧ (∀ j, s.d j ≤ t.d j)

/-- The box `[l₁, u₁] × ⋯ × [l_N, u_N]`: all data whose every entry lies between
the corresponding entries of `l` and `u`. -/
def dataBox {m n₁ n₂ : ℕ} (l u : ScenarioData m n₁ n₂) : Set (ScenarioData m n₁ n₂) :=
  {s | DataLE l s ∧ DataLE s u}

/-- Definition 1.1 (p. 5) in `ℝ^N`: `U` is a hypercube if `U = [l₁, u₁] × ⋯ × [l_N, u_N]`
for some `lᵢ ≤ uᵢ`, `i = 1, …, N`. -/
def IsHypercube {m n₁ n₂ : ℕ} (U : Set (ScenarioData m n₁ n₂)) : Prop :=
  ∃ l u : ScenarioData m n₁ n₂, DataLE l u ∧ U = dataBox l u

/-- The uncertainty set of §5.3 (p. 31),
`U = {(A(ω), B(ω), b(ω), d(ω)) | ω ∈ Ω}`. -/
def uncertaintySet {m n₁ n₂ : ℕ} {Ω : Type*}
    (A : Ω → Matrix (Fin m) (Fin n₁) ℝ)
    (B : Ω → Matrix (Fin m) (Fin n₂) ℝ)
    (b : Ω → Fin m → ℝ) (d : Ω → Fin n₂ → ℝ) : Set (ScenarioData m n₁ n₂) :=
  Set.range fun ω => (⟨A ω, B ω, b ω, d ω⟩ : ScenarioData m n₁ n₂)

end RobustPower.Hypercube


