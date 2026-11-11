-- Prove2me | Definitions.Def_DistQuantumQuery_muMat
-- name    : DistQuantumQuery_muMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:14:03.776007+00:00
-- url     : https://prove2.me/theorems/0dfcba8a-e276-42be-85f8-65dbae179157
-- title:
--   Distributions, $|\mu\rangle\langle\mu|$, all-ones $J$, query filters $\Delta_i$, agreement and disagreement matrices $A_f$, $\Delta_f$
-- statement:
--   Let $\Sigma$ be a finite set. A **distribution** is $\mu:\Sigma\to[0,1]$ with $\sum_x\mu(x)=1$; its unit vector is $|\mu\rangle:=\sum_x\sqrt{\mu(x)}\,|x\rangle$, and $|\mu\rangle\langle\mu|$ has entries $\sqrt{\mu(x)\mu(y)}$. $J$ is the all-ones matrix.
--
--   For an input set $\Sigma\subseteq\{0,1\}^n$ and a position $i$, the **input-disagreement matrix** (query filter) is
--   $$
--   \Delta_i(x,y):=\mathbb 1[x_i\ne y_i].
--   $$
--   For a functional problem $f:\Sigma\to\Omega$ the **agreement** and **disagreement** matrices are $A_f(x,y):=\mathbb 1[f(x)=f(y)]$ and $\Delta_f(x,y):=\mathbb 1[f(x)\ne f(y)]$, so $A_f=J-\Delta_f$. A functional problem is the search problem whose valid outputs at $x$ are $\{f(x)\}$.
--
--   These matrices are the filters and targets of every adversary measure of the paper.
--
--   **Formalization Note** The filter is defined for any input set whose elements carry bit strings; for $\Sigma$ the bits are the elements themselves, and the same definition gives the filters $\Delta_{ij}$ of a composed input (block $i$, bit $j$). Positions form an arbitrary finite type.
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.1 p.11 (distributions, |µ⟩), §2.4 p.17 (search, functional problems), §2.4.1 p.17 (∆i, ∆f, Af)

import Mathlib

open scoped Matrix

namespace DistQuantumQuery

/-- `μ : X → [0,1]` is a **probability distribution**: nonnegative weights summing to one
(Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*, arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.1, p.11). -/
def IsDist {X : Type*} [Fintype X] (μ : X → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ ∑ x, μ x = 1

/-- The vector `|μ⟩ := Σ_x √μ(x) |x⟩` (arXiv:2610.06835, held version, §2.1, p.11). -/
noncomputable def muKet {X : Type*} (μ : X → ℝ) : X → ℂ :=
  fun x => ((Real.sqrt (μ x) : ℝ) : ℂ)

/-- The rank-one matrix `|μ⟩⟨μ|`, with entries `√(μ(x)μ(y))` (arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.1, p.11). -/
noncomputable def muMat {X : Type*} (μ : X → ℝ) : Matrix X X ℂ :=
  Matrix.vecMulVec (muKet μ) (star (muKet μ))

/-- The all-ones matrix `J` (arXiv:2610.06835, held version, §2.1, p.11). -/
def allOnes (X : Type*) : Matrix X X ℂ :=
  Matrix.of fun _ _ => 1

/-- The **input-disagreement matrix** (query filter) `Δ_p(x, y) := 1[x_p ≠ y_p]` for an input set
`X` whose elements carry bit strings `b x : P → Bool` (arXiv:2610.06835, held version,
sha256 6334ffaf…, §2.4.1, p.17).

**Formalization Note** The paper's inputs are bit strings `x ∈ Σ ⊆ {0,1}^n`; here `b` reads off
the bits, so the same definition serves `Σ` (with `b = Subtype.val`), `{0,1}^n` (with `b = id`)
and `Σ_g^n` (with `b x (i, j) =` bit `j` of block `i`, the filters `Δ_{ij}` of p.61). -/
def qfilt {X P : Type*} (b : X → P → Bool) (p : P) : Matrix X X ℂ :=
  Matrix.of fun x y => if b x p = b y p then 0 else 1

/-- The query filters `{Δ_i}_{i ∈ [n]}` on an input set `Σ ⊆ {0,1}^ι`, `Δ_i(x, y) = 1[x_i ≠ y_i]`
(arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.1, p.17).

**Formalization Note** The positions `[n]` are an arbitrary finite type `ι`; `Σ` is a `Finset`
of bit strings `ι → Bool` and matrices are indexed by its elements. -/
def qfilters {ι : Type*} (S : Finset (ι → Bool)) : ι → Matrix S S ℂ :=
  qfilt (fun x : S => x.1)

/-- The **agreement matrix** `A_f(x, y) := 1[f(x) = f(y)]` of a functional problem
`f : Σ → Ω` (arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.1, p.17). -/
def agree {X Ω : Type*} [DecidableEq Ω] (f : X → Ω) : Matrix X X ℂ :=
  Matrix.of fun x y => if f x = f y then 1 else 0

/-- The **disagreement matrix** `Δ_f(x, y) := 1[f(x) ≠ f(y)] = (J − A_f)(x, y)`
(arXiv:2610.06835, held version, sha256 6334ffaf…, §2.4.1, p.17). -/
def disagree {X Ω : Type*} [DecidableEq Ω] (f : X → Ω) : Matrix X X ℂ :=
  Matrix.of fun x y => if f x = f y then 0 else 1

/-- The relation `{(x, s) : s = f(x)}` of a functional problem `f : Σ → Ω`, i.e. the search
problem in which every `f(x)` is the singleton `{f(x)}` (arXiv:2610.06835, held version, §2.4,
p.17). -/
def graphRel {X Ω : Type*} (f : X → Ω) : X → Ω → Prop :=
  fun x s => s = f x

end DistQuantumQuery


