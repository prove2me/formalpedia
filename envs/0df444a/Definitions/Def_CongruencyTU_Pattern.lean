-- Prove2me | Definitions.Def_CongruencyTU_Pattern
-- name    : CongruencyTU_Pattern
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T02:45:48.626978+00:00
-- url     : https://prove2.me/theorems/e75d8269-9e15-47da-b90b-321ad3d2987b
-- title:
--   Problems of form (1), scalar products, narrowed patterns, linear (sub-)patterns and system (3)
-- statement:
--   When the constraint matrix is a 1-, 2- or 3-sum, an R-CCTUF problem has the **form (1)**
--   $$\begin{pmatrix}A&ef^\top\\gh^\top&B\end{pmatrix}\begin{pmatrix}x_A\\x_B\end{pmatrix}\le\begin{pmatrix}b_A\\b_B\end{pmatrix},\qquad \gamma_A^\top x_A+\gamma_B^\top x_B\in R\pmod m,\qquad x_A\in\mathbb Z^{n_A},\ x_B\in\mathbb Z^{n_B},$$
--   with $g=h=0$ for a 2-sum and also $e=f=0$ for a 1-sum. For $\alpha:=f^\top x_B$ and $\beta:=h^\top x_A$ it splits into the **A-problem** $Ax_A\le b_A-\alpha e$, $h^\top x_A=\beta$ and the **B-problem** $Bx_B\le b_B-\beta g$, $f^\top x_B=\alpha$ (each with a congruency constraint). A solution is **for** $(\alpha,\beta)$ if $f^\top x_B=\alpha$ and $h^\top x_A=\beta$.
--
--   1. $\Pi\subseteq\mathbb Z^2$ is the set of $(\alpha,\beta)$ for which both (relaxed) problems are feasible.
--   2. For bounds $\ell_i,u_i$ from Lemma 16, $\Pi_{\mathrm{narrowed}}=\Pi\cap\{\ell_0\le\alpha+\beta\le u_0,\ \ell_1\le\alpha\le u_1,\ \ell_2\le\beta\le u_2\}$.
--   3. The **narrowed pattern** $\pi:\Pi_{\mathrm{narrowed}}\to 2^{\{0,\dots,m-1\}}$ sends $(\alpha,\beta)$ to the residues $r_B$ for which the B-problem with $\gamma_B^\top x_B\equiv r_B$ is feasible.
--   4. $\pi$ is **linear** on a domain $D$ (Definition 17) if $|\pi(\alpha,\beta)|=1$ there and the residue is $\equiv r_0+r_1\alpha+r_2\beta\pmod m$ for fixed $r_0,r_1,r_2\in\mathbb Z$.
--   5. A **sub-pattern** $\tilde\pi$ (Definition 61) has a domain of the same hexagonal shape contained in $\Pi_{\mathrm{narrowed}}$ and $\tilde\pi(\alpha,\beta)\subseteq\pi(\alpha,\beta)$; a solution is **covered** by it if $\gamma_B^\top x_B\in\tilde\pi(\alpha,\beta)$.
--   6. **System (3)** of Theorem 18 is the R-CCTUF problem in $(x_A,y_1,y_2)$ with $Ax_A+ey_1\le b_A$, $h^\top x_A-y_2=0$, $\ell_0\le y_1+y_2\le u_0$, $\ell_1\le y_1\le u_1$, $\ell_2\le y_2\le u_2$ and $\gamma_A^\top x_A+r_1y_1+r_2y_2\in r_0+R\pmod m$.
--
--   **Formalization Note** A problem of form (1) is a `Form1`; `Form1.Valid` asks that the two 3-sum summands are totally unimodular (this covers 1- and 2-sums with zero vectors). Bounds are indexed $0$ for $\alpha+\beta$, $1$ for $\alpha$, $2$ for $\beta$. `Lemma16Bounds` is Lemma 16's guarantee; `patternTable` lists the narrowed pattern as a finite table; `sys3` writes the equation and two-sided bounds of (3) as pairs of inequalities; `SolvesSmallRInst` is the oracle of Theorem 22.
-- source:
--   Nägele, Santiago, Zenklusen, Congruency-Constrained TU Problems Beyond the Bimodular Case, arXiv:2109.03148v3 [math.OC] (preprint, 25 Apr 2023), https://arxiv.org/abs/2109.03148v3, (1), (2), Π, Lemma 16, p.9 (PDF p.10); Π_narrowed and narrowed pattern, p.10; Definition 17 and (3), p.11; (21), p.36; p.39; Definition 61, p.43; Theorem 22, p.13

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_CongruencyTU_Instance
import Definitions.Def_CongruencyTU_Sums

open Classical Matrix

namespace CongruencyTU

/-! # Problems of form (1), scalar products, narrowed patterns, linear (sub-)patterns, system (3)

Nägele–Santiago–Zenklusen, arXiv:2109.03148v3 (preprint):
* form (1), the A- and B-problems (2), the set `Π`, p.9 (PDF p.10); `Π_narrowed`, p.10 and (21),
  p.36; narrowed pattern, p.10 (PDF p.11); Lemma 16's bounds, p.9;
* Definition 17 (linear), p.11 (PDF p.12); system (3) of Theorem 18, p.11;
* "solution for `(α, β)`", p.39 (PDF p.40); Definition 61 (sub-pattern, covered), p.43 (PDF p.44).

If the constraint matrix decomposes as a 1-, 2- or 3-sum (Theorem 14 (iii)), the R-CCTUF problem is
`(A ef⊤; gh⊤ B)(x_A; x_B) ≤ (b_A; b_B)`, `γ_A⊤x_A + γ_B⊤x_B ∈ R (mod m)`, `x_A ∈ ℤ^{nA}`,
`x_B ∈ ℤ^{nB}` (form (1)); for a 2-sum `g, h` are zero and for a 1-sum also `e, f`. With
`α := f⊤x_B`, `β := h⊤x_A` the problem splits into the A-problem `A x_A ≤ b_A − αe, h⊤x_A = β` and
the B-problem `B x_B ≤ b_B − βg, f⊤x_B = α` (each with its congruency constraint). `Π ⊆ ℤ²` is the
set of `(α, β)` for which (the relaxations of) both problems are feasible; `Π_narrowed` is `Π`
intersected with `ℓ₀ ≤ α + β ≤ u₀, ℓ₁ ≤ α ≤ u₁, ℓ₂ ≤ β ≤ u₂` for the bounds `ℓᵢ, uᵢ` of Lemma 16;
the narrowed pattern `π : Π_narrowed → 2^{0,…,m−1}` sends `(α, β)` to the residues `r_B` for which
the B-problem is feasible.

**Formalization Note.**
* A problem of form (1) is a `Form1`; `Form1.Valid` asks that the two 3-sum summands
  `(A e e; h⊤ 0 1)` and `(0 1 f⊤; g g B)` are totally unimodular, as they are in case (iii) of
  Theorem 14. With `g = h = 0` these are TU exactly when the 2-sum summands `(A e)`, `(f⊤; B)` are,
  and with `e = f = g = h = 0` exactly when `A` and `B` are, so the one condition covers 1-, 2- and
  3-sums; the matrix `(A ef⊤; gh⊤ B)` itself is then TU (p.8: a 3-sum is TU iff its summands are).
* `Π` uses the relaxations (no congruency constraint) of the A- and B-problems, as Lemma 55 (p.37)
  and the pattern (whose values are the feasible residues) require.
* The bounds are `ℓ u : Fin 3 → ℤ`, index `0` for `α + β`, `1` for `α`, `2` for `β`.
  `Lemma16Bounds` states exactly the guarantee of Lemma 16 (widths `uᵢ − ℓᵢ ≤ m − |R|`, and a
  solution within the bounds if the problem is feasible); the narrowed pattern is the restriction of
  `pattern` to `narrowed ℓ u`.
* Residues are elements of `{0, …, m − 1}` (`Finset ℕ`); a congruence `γ_B⊤x_B ∈ π(α, β)` is read
  modulo `m`. -/

/-- A problem of form (1). -/
structure Form1 where
  kA : ℕ
  nA : ℕ
  kB : ℕ
  nB : ℕ
  A : Matrix (Fin kA) (Fin nA) ℤ
  B : Matrix (Fin kB) (Fin nB) ℤ
  e : Fin kA → ℤ
  f : Fin nB → ℤ
  g : Fin kB → ℤ
  h : Fin nA → ℤ
  bA : Fin kA → ℤ
  bB : Fin kB → ℤ
  m : ℕ
  γA : Fin nA → ℤ
  γB : Fin nB → ℤ
  R : Finset ℕ

/-- `z ∈ R (mod m)`: `z ≡ r (mod m)` for some `r ∈ R`. -/
def InRes (m : ℕ) (R : Finset ℕ) (z : ℤ) : Prop := ∃ r ∈ R, z ≡ (r : ℤ) [ZMOD (m : ℤ)]

/-- The "hexagon" `{(α, β) ∈ ℤ² : ℓ₀ ≤ α + β ≤ u₀, ℓ₁ ≤ α ≤ u₁, ℓ₂ ≤ β ≤ u₂}`. -/
def hexagon (ℓ u : Fin 3 → ℤ) : Set (ℤ × ℤ) :=
  {p | ℓ 0 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ u 0 ∧ ℓ 1 ≤ p.1 ∧ p.1 ≤ u 1 ∧ ℓ 2 ≤ p.2 ∧ p.2 ≤ u 2}

/-- **Linear** (Definition 17): `|π(α, β)| = 1` on `D`, and for some `r₀, r₁, r₂ ∈ ℤ` the single
residue `r(α, β)` satisfies `r(α, β) ≡ r₀ + r₁α + r₂β (mod m)` on `D`. -/
def IsLinearOn (m : ℕ) (D : Set (ℤ × ℤ)) (π : ℤ × ℤ → Finset ℕ) : Prop :=
  (∀ p ∈ D, (π p).card = 1) ∧
  ∃ r₀ r₁ r₂ : ℤ, ∀ p ∈ D, ∀ r ∈ π p, (r : ℤ) ≡ r₀ + r₁ * p.1 + r₂ * p.2 [ZMOD (m : ℤ)]

namespace Form1

variable (F : Form1)

/-- Summands TU and `m > 0`, `R ⊆ {0, …, m − 1}` (see the module note). -/
def Valid : Prop :=
  (sum3Left F.A F.e F.h).IsTotallyUnimodular ∧ (sum3Right F.f F.g F.B).IsTotallyUnimodular ∧
  0 < F.m ∧ ∀ r ∈ F.R, r < F.m

/-- `(x_A, x_B)` solves the relaxation of (1). -/
def Relaxed (xA : Fin F.nA → ℤ) (xB : Fin F.nB → ℤ) : Prop :=
  F.A *ᵥ xA + (F.f ⬝ᵥ xB) • F.e ≤ F.bA ∧ (F.h ⬝ᵥ xA) • F.g + F.B *ᵥ xB ≤ F.bB

/-- `(x_A, x_B)` is a feasible solution of (1). -/
def IsSol (xA : Fin F.nA → ℤ) (xB : Fin F.nB → ℤ) : Prop :=
  F.Relaxed xA xB ∧ InRes F.m F.R (F.γA ⬝ᵥ xA + F.γB ⬝ᵥ xB)

/-- (1) is feasible. -/
def Feasible : Prop := ∃ xA xB, F.IsSol xA xB

/-- `(x_A, x_B)` is a solution **for** `(α, β)`: `f⊤x_B = α` and `h⊤x_A = β` (p.39). -/
def For (α β : ℤ) (xA : Fin F.nA → ℤ) (xB : Fin F.nB → ℤ) : Prop :=
  F.f ⬝ᵥ xB = α ∧ F.h ⬝ᵥ xA = β

/-- `x_A` solves the relaxation of the A-problem for `(α, β)`: `A x_A ≤ b_A − αe`, `h⊤x_A = β`. -/
def RelA (α β : ℤ) (xA : Fin F.nA → ℤ) : Prop :=
  F.A *ᵥ xA ≤ F.bA - α • F.e ∧ F.h ⬝ᵥ xA = β

/-- `x_B` solves the relaxation of the B-problem for `(α, β)`: `B x_B ≤ b_B − βg`, `f⊤x_B = α`. -/
def RelB (α β : ℤ) (xB : Fin F.nB → ℤ) : Prop :=
  F.B *ᵥ xB ≤ F.bB - β • F.g ∧ F.f ⬝ᵥ xB = α

/-- `Π`: the pairs `(α, β)` for which the relaxations of both the A- and the B-problem are
feasible. -/
def PiSet : Set (ℤ × ℤ) := {p | (∃ xA, F.RelA p.1 p.2 xA) ∧ ∃ xB, F.RelB p.1 p.2 xB}

/-- `Π_narrowed = Π ∩ {ℓ₀ ≤ α + β ≤ u₀, ℓ₁ ≤ α ≤ u₁, ℓ₂ ≤ β ≤ u₂}` ((21), p.36). -/
def narrowed (ℓ u : Fin 3 → ℤ) : Set (ℤ × ℤ) := F.PiSet ∩ hexagon ℓ u

/-- The (global) pattern: the residues `r_B ∈ {0, …, m − 1}` for which the B-problem for
`(α, β)` is feasible. Its restriction to `narrowed ℓ u` is the narrowed pattern. -/
noncomputable def pattern (p : ℤ × ℤ) : Finset ℕ :=
  (Finset.range F.m).filter fun r =>
    ∃ xB, F.RelB p.1 p.2 xB ∧ F.γB ⬝ᵥ xB ≡ (r : ℤ) [ZMOD (F.m : ℤ)]

/-- The guarantee of Lemma 16 (p.9) for bounds `ℓ, u`: `uᵢ − ℓᵢ ≤ m − |R|`, and if (1) has a
solution then it has one with `(α, β)` in the hexagon. -/
def Lemma16Bounds (ℓ u : Fin 3 → ℤ) : Prop :=
  (∀ i, u i - ℓ i ≤ (F.m : ℤ) - F.R.card) ∧
  (F.Feasible → ∃ xA xB, F.IsSol xA xB ∧ (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA) ∈ hexagon ℓ u)

/-- **Sub-pattern** (Definition 61): `π̃` with domain `D̃` is a sub-pattern of the narrowed pattern
for the bounds `ℓ, u` if (i) `D̃ ⊆ Π_narrowed`, (ii) `D̃` is a hexagon for some bounds, and (iii)
`π̃(α, β) ⊆ π(α, β)` on `D̃`. -/
def IsSubPattern (ℓ u : Fin 3 → ℤ) (D : Set (ℤ × ℤ)) (π' : ℤ × ℤ → Finset ℕ) : Prop :=
  D ⊆ F.narrowed ℓ u ∧ (∃ ℓ' u' : Fin 3 → ℤ, D = hexagon ℓ' u') ∧ ∀ p ∈ D, π' p ⊆ F.pattern p

/-- A solution `(x_A, x_B)` is **covered** by `π̃` (Definition 61): `γ_B⊤x_B ∈ π̃(α, β)` (modulo
`m`) for `α = f⊤x_B`, `β = h⊤x_A`. -/
def Covered (π' : ℤ × ℤ → Finset ℕ) (xA : Fin F.nA → ℤ) (xB : Fin F.nB → ℤ) : Prop :=
  InRes F.m (π' (F.f ⬝ᵥ xB, F.h ⬝ᵥ xA)) (F.γB ⬝ᵥ xB)

/-- Encoding `[kA, nA, kB, nB, m] ++ A ++ B ++ e ++ f ++ g ++ h ++ b_A ++ b_B ++ γ_A ++ γ_B ++ R`. -/
def enc : List ℤ :=
  [(F.kA : ℤ), (F.nA : ℤ), (F.kB : ℤ), (F.nB : ℤ), (F.m : ℤ)] ++ encMat F.A ++ encMat F.B ++
  encVec F.e ++ encVec F.f ++ encVec F.g ++ encVec F.h ++ encVec F.bA ++ encVec F.bB ++
  encVec F.γA ++ encVec F.γB ++ encRes F.R

/-- The narrowed pattern as a finite table: for `α = ℓ₁, …, u₁` (outer) and `β = ℓ₂, …, u₂`
(inner), the block `[0]` if `(α, β) ∉ Π_narrowed`, and `1 :: |π(α, β)| :: π(α, β)` (increasing)
otherwise; blocks framed by `pack`. -/
noncomputable def patternTable (ℓ u : Fin 3 → ℤ) : List ℤ :=
  pack ((List.range (u 1 - ℓ 1 + 1).toNat).flatMap fun a =>
    (List.range (u 2 - ℓ 2 + 1).toNat).map fun b =>
      if ((ℓ 1 + a, ℓ 2 + b) : ℤ × ℤ) ∈ F.narrowed ℓ u then
        1 :: encRes (F.pattern ((ℓ 1 + a, ℓ 2 + b) : ℤ × ℤ))
      else [0])

/-- The R-CCTUF problem of form (1) as an `RInst` on `nA + nB` variables (rows `A`-block first,
columns `x_A` first). -/
noncomputable def toRInst : RInst where
  k := F.kA + F.kB
  n := F.nA + F.nB
  T := (sum3 F.A F.e F.f F.g F.h F.B).reindex finSumFinEquiv finSumFinEquiv
  b := fun i => Sum.elim F.bA F.bB (finSumFinEquiv.symm i)
  m := F.m
  γ := fun j => Sum.elim F.γA F.γB (finSumFinEquiv.symm j)
  R := F.R

/-- The constraint matrix of system (3) of Theorem 18 (p.11) in the variables `(x_A, y₁, y₂)`, the
equation `h⊤x_A − y₂ = 0` and each two-sided bound written as two inequalities:
`A x_A + e y₁ ≤ b_A`, `h⊤x_A − y₂ ≤ 0`, `−h⊤x_A + y₂ ≤ 0`, `y₁ + y₂ ≤ u₀`, `−y₁ − y₂ ≤ −ℓ₀`,
`y₁ ≤ u₁`, `−y₁ ≤ −ℓ₁`, `y₂ ≤ u₂`, `−y₂ ≤ −ℓ₂`. -/
noncomputable def sys3Mat : Matrix (Fin F.kA ⊕ Fin 8) (Fin F.nA ⊕ Fin 2) ℤ :=
  fromBlocks F.A (of fun i j => if j = 0 then F.e i else 0)
    (of fun r j => if r = 0 then F.h j else if r = 1 then -F.h j else 0)
    !![0, -1; 0, 1; 1, 1; -1, -1; 1, 0; -1, 0; 0, 1; 0, -1]

/-- **System (3)** of Theorem 18 as an R-CCTUF problem on `nA + 2` variables `(x_A, y₁, y₂)`:
constraint matrix `sys3Mat`, right-hand side `(b_A, 0, 0, u₀, −ℓ₀, u₁, −ℓ₁, u₂, −ℓ₂)`, congruency
`γ_A⊤x_A + r₁y₁ + r₂y₂ ∈ r₀ + R (mod m)`, i.e. target residues `{(r₀ + r) mod m : r ∈ R}`. -/
noncomputable def sys3 (ℓ u : Fin 3 → ℤ) (r₀ r₁ r₂ : ℤ) : RInst where
  k := F.kA + 8
  n := F.nA + 2
  T := F.sys3Mat.reindex finSumFinEquiv finSumFinEquiv
  b := fun i => Sum.elim F.bA ![0, 0, u 0, -ℓ 0, u 1, -ℓ 1, u 2, -ℓ 2] (finSumFinEquiv.symm i)
  m := F.m
  γ := fun j => Sum.elim F.γA ![r₁, r₂] (finSumFinEquiv.symm j)
  R := F.R.image fun r => ((r₀ + (r : ℤ)) % (F.m : ℤ)).toNat

end Form1

/-- The linear pattern with parameters `r₀, r₁, r₂`: `(α, β) ↦ {(r₀ + r₁α + r₂β) mod m}`. -/
noncomputable def linPat (m : ℕ) (r₀ r₁ r₂ : ℤ) (p : ℤ × ℤ) : Finset ℕ :=
  {((r₀ + r₁ * p.1 + r₂ * p.2) % (m : ℤ)).toNat}

/-- **Oracle for small R-CCTUF problems** (Theorem 22, p.13): on the encoding of every valid R-CCTUF
problem with `p` variables, modulus `m` and at most `ℓ` target residues, the oracle answers `[0]` if
the problem is infeasible and `1 :: x` with `x` a feasible solution otherwise. Its answers on other
queries are unconstrained. -/
def SolvesSmallRInst (m ℓ p : ℕ) (O : Oracle) : Prop :=
  ∀ Q : RInst, Q.Valid → Q.n = p → Q.m = m → Q.R.card ≤ ℓ →
    (¬ Q.Feasible → O Q.enc = [0]) ∧ (Q.Feasible → Q.SolOut (O Q.enc))

end CongruencyTU


