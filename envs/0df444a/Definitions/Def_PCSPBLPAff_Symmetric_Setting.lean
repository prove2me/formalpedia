-- Prove2me | Definitions.Def_PCSPBLPAff_Symmetric_Setting
-- name    : PCSPBLPAff_Symmetric_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T19:02:35.6738+00:00
-- url     : https://prove2.me/theorems/3a435105-5681-4d5d-9724-ca7520feede4
-- title:
--   §2–§4, pp. 4–8 — relational structures, PCSP instances, polymorphisms, the Basic LP (1)–(5), the affine relaxation (6)–(8), the BLP+Affine algorithm (Figure 1) and Definition 1
-- statement:
--   This module fixes the setting of §2–§4 of Brakensiek, Guruswami, Wrochna and Živný.
--
--   1. **Signature and structures.** A signature is a set $\tau$ of symbols, each with an arity $\mathrm{ar}(R)\in\mathbb N$. A relational structure $\mathbf A$ on a domain $A$ assigns to each $R\in\tau$ a relation $R^{\mathbf A}\subseteq A^{\mathrm{ar}(R)}$. A map $\sigma:A\to B$ is a **homomorphism** $\mathbf A\to\mathbf B$ if $\sigma(R^{\mathbf A})\subseteq R^{\mathbf B}$ for all $R$ (componentwise), and $(\mathbf A,\mathbf B)$ is a **promise template** if such a homomorphism exists.
--   2. **Instances.** An instance $X$ has variables $x_1,\dots,x_n$ and constraints $c_j=(R_j,\bar x_j)$, $j\in[m]$, where $\bar x_j$ is a tuple of $\mathrm{ar}(R_j)$ variables (repetitions allowed). $X$ is **satisfiable in** $\mathbf A$ if some $\sigma:\{x_1,\dots,x_n\}\to A$ has $\sigma(\bar x_j)\in R_j^{\mathbf A}$ for every $j$.
--   3. **Polymorphisms.** $f:A^L\to B$ is a polymorphism of $(\mathbf A,\mathbf B)$ if, for every $R$ and every $L\times\mathrm{ar}(R)$ matrix whose rows lie in $R^{\mathbf A}$, applying $f$ to each column gives a tuple in $R^{\mathbf B}$. It is **symmetric** if $f(x_1,\dots,x_L)=f(x_{\pi(1)},\dots,x_{\pi(L)})$ for all $\pi\in S_L$. It is **block-symmetric of width at least $N$** if for some partition $[L]=B_1\cup\dots\cup B_\kappa$ into $\kappa\ge1$ blocks, each of size at least $N$, $f$ is invariant under permutations of the coordinates within each block.
--   4. **Basic LP** $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$: rational weights $w_i(a)$ and $p_j(y)$ with
--   $$
--   w_i(a)\ge0,\quad p_j(y)\ge0,\quad \sum_{a\in A}w_i(a)=1,\quad \sum_{y\in R_j^{\mathbf A}}p_j(y)=1,\quad \sum_{y\in R_j^{\mathbf A},\,y_k=a}p_j(y)=w_i(a)
--   $$
--   whenever $x_i$ is the $k$-th variable of $\bar x_j$.
--   5. **Affine relaxation** $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$: the same equations (without sign constraints) in integer unknowns $r_i(a)$, $q_j(y)$.
--   6. **Maximal-support solution.** A solution $(w,p)$ of $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ in which every coordinate is positive if and only if it is positive at some point of the polytope (the property of a relative interior point used by the algorithm).
--   7. **The BLP+Affine algorithm** (Figure 1) **accepts** $X$ if $\mathrm{LP}_{\mathbb Q}(X,\mathbf A)$ has a maximal-support solution $(w,p)$ and the refined lattice $\mathrm{Aff}'_{\mathbb Z}(X,\mathbf A)$, consisting of the solutions $(r,q)$ of $\mathrm{Aff}_{\mathbb Z}(X,\mathbf A)$ with $r_i(a)=0$ whenever $w_i(a)=0$ and $q_j(y)=0$ whenever $p_j(y)=0$, is nonempty. It does not depend on $\mathbf B$.
--   8. **Definition 1.** The algorithm **correctly solves** $\mathrm{PCSP\text{-}Decision}(\mathbf A,\mathbf B)$ if it accepts every instance satisfiable in $\mathbf A$ and rejects every instance unsatisfiable in $\mathbf B$.
--
--   These objects are the vocabulary of Theorems 2 and 3, which identify polymorphism conditions under which this single algorithm decides the promise problem.
--
--   **Formalization Note** Variables are `Fin n` and constraints `Fin m`; a constraint's scope is a function `Fin (ar R_j) → Fin n`. The weights $p_j$, $q_j$ are functions on all of $A^{\mathrm{ar}(R_j)}$ required to vanish off $R_j^{\mathbf A}$, which is equivalent to indexing them by $R_j^{\mathbf A}$. The marginal conditions (5) and (8) are imposed for each position $k$ of the scope, which settles the case of a variable repeated in a constraint. The relative interior point is encoded by its maximal-support property (footnote 1); all such points have the same zero set, so acceptance does not depend on the choice. The page's "positive integer arity" is relaxed to any arity in $\mathbb N$. The width requires at least one block, as footnote 2 presumes. The helper `HasCounts x W` says the tuple $x\in A^L$ contains each $a$ exactly $W(a)$ times.
-- source:
--   arXiv:1907.04383v3, §2 and §2.1–§2.2 (p. 4), §2.3 with (1)–(8) and footnote 1 (p. 5), §3, Figure 1 and Definition 1 (pp. 5–6), §4 and footnote 2 (p. 8)

import Mathlib

namespace PCSPBLPAff.Symmetric

/-- A relational structure with signature `τ` (arities `ar`) on the domain `A`: one relation
`R^A ⊆ A^{ar(R)}` for each symbol `R ∈ τ` (arXiv:1907.04383v3, §2, p. 4). -/
structure RelStruct (τ : Type) (ar : τ → ℕ) (A : Type) where
  rel : (R : τ) → Set (Fin (ar R) → A)

/-- `σ : A → B` is a homomorphism `𝔸 → 𝔹`: `σ(R^A) ⊆ R^B` for all `R ∈ τ`, with `σ` applied
to a tuple component-wise (§2, p. 4). -/
def IsHom {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B)
    (σ : A → B) : Prop :=
  ∀ R : τ, ∀ t ∈ 𝔸.rel R, σ ∘ t ∈ 𝔹.rel R

/-- `(𝔸, 𝔹)` is a promise template: there is a homomorphism from `𝔸` to `𝔹` (§2, p. 4). -/
def IsPromiseTemplate {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A)
    (𝔹 : RelStruct τ ar B) : Prop :=
  ∃ σ : A → B, IsHom 𝔸 𝔹 σ

/-- An instance of `PCSP(𝔸, 𝔹)` (§2.1, p. 4): variables `x_1, …, x_n` (as `Fin n`) and
constraints `c_j = (R_j, x̄_j)` for `j : Fin m`, where `R_j = sym j` and `x̄_j = scope j` is a
tuple of variables of arity `ar(R_j)` (a variable may occur several times). -/
structure Instance (τ : Type) (ar : τ → ℕ) where
  n : ℕ
  m : ℕ
  sym : Fin m → τ
  scope : (j : Fin m) → Fin (ar (sym j)) → Fin n

/-- `X` is satisfiable in the structure `𝔸`: some assignment `σ` of the variables sends every
constraint tuple `x̄_j` into `R_j^A` (§2.1, p. 4). -/
def SatIn {τ : Type} {ar : τ → ℕ} {A : Type} (X : Instance τ ar) (𝔸 : RelStruct τ ar A) : Prop :=
  ∃ σ : Fin X.n → A, ∀ j : Fin X.m, σ ∘ X.scope j ∈ 𝔸.rel (X.sym j)

/-- `f : A^L → B` is a polymorphism of `(𝔸, 𝔹)` (§2.2, p. 4): for every relation symbol `R`
and every `L × ar(R)` matrix `M` whose rows `M l` lie in `R^A`, the tuple obtained by
applying `f` to each column lies in `R^B`. -/
def IsPolymorphism {τ : Type} {ar : τ → ℕ} {A B : Type} (𝔸 : RelStruct τ ar A)
    (𝔹 : RelStruct τ ar B) {L : ℕ} (f : (Fin L → A) → B) : Prop :=
  ∀ (R : τ) (M : Fin L → Fin (ar R) → A), (∀ l, M l ∈ 𝔸.rel R) →
    (fun c => f (fun l => M l c)) ∈ 𝔹.rel R

/-- `f : A^L → B` is symmetric: `f(x_1, …, x_L) = f(x_{π(1)}, …, x_{π(L)})` for every
permutation `π ∈ S_L` (§2.2, p. 4). -/
def IsSymmetric {A B : Type} {L : ℕ} (f : (Fin L → A) → B) : Prop :=
  ∀ (π : Equiv.Perm (Fin L)) (x : Fin L → A), f (x ∘ π) = f x

/-- `f` is permutation-invariant within each block of the partition of `[L]` given by the
block labelling `β` (block `b` is `β⁻¹(b)`) (§4, p. 8). -/
def IsBlockSymmetricFor {A B : Type} {L κ : ℕ} (β : Fin L → Fin κ) (f : (Fin L → A) → B) :
    Prop :=
  ∀ π : Equiv.Perm (Fin L), (∀ l, β (π l) = β l) → ∀ x : Fin L → A, f (x ∘ π) = f x

/-- `f` is block-symmetric of width at least `N` (§4, p. 8 and footnote 2): for some partition
of `[L]` into `κ ≥ 1` blocks, every block has at least `N` elements and `f` is invariant under
permutations within each block. -/
def HasWidthAtLeast {A B : Type} {L : ℕ} (f : (Fin L → A) → B) (N : ℕ) : Prop :=
  ∃ (κ : ℕ) (β : Fin L → Fin κ), 0 < κ ∧
    (∀ b, N ≤ (Finset.univ.filter (fun l => β l = b)).card) ∧ IsBlockSymmetricFor β f

/-- `x : Fin L → A` contains each `a` exactly `W a` times (the input
"a, …, a (W_i(a) times) ∀ a ∈ A", p. 7). -/
def HasCounts {A : Type} [DecidableEq A] {L : ℕ} (x : Fin L → A) (W : A → ℕ) : Prop :=
  ∀ a, (Finset.univ.filter (fun l => x l = a)).card = W a

/-- `(w, p)` is a point of the Basic LP polytope `LP_ℚ(X, 𝔸)`, constraints (1)–(5) (§2.3,
p. 5). `p j` is a function on all tuples that vanishes off `R_j^A`; the marginal condition
(5) is imposed for each position `k` of the scope `x̄_j`. -/
def IsLPSol {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) : Prop :=
  (∀ i a, 0 ≤ w i a) ∧
  (∀ j y, 0 ≤ p j y) ∧
  (∀ j y, y ∉ 𝔸.rel (X.sym j) → p j y = 0) ∧
  (∀ i, ∑ a, w i a = 1) ∧
  (∀ j, ∑ y, p j y = 1) ∧
  (∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
    ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a), p j y =
      w (X.scope j k) a)

/-- `(r, q)` is a point of the affine relaxation `Aff_ℤ(X, 𝔸)`, equations (6)–(8) (§2.3,
p. 5): integer (possibly negative) weights, `q j` vanishing off `R_j^A`, marginals per
position of the scope. -/
def IsAffSol {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (r : Fin X.n → A → ℤ)
    (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ) : Prop :=
  (∀ j y, y ∉ 𝔸.rel (X.sym j) → q j y = 0) ∧
  (∀ i, ∑ a, r i a = 1) ∧
  (∀ j, ∑ y, q j y = 1) ∧
  (∀ (j : Fin X.m) (k : Fin (ar (X.sym j))) (a : A),
    ∑ y ∈ Finset.univ.filter (fun y : Fin (ar (X.sym j)) → A => y k = a), q j y =
      r (X.scope j k) a)

/-- `(w, p)` is a solution of `LP_ℚ(X, 𝔸)` of maximal support: each coordinate is nonzero
(equivalently positive) if it is nonzero at some point of the polytope. This is the property
of a relative interior point used by the algorithm (§2.3, p. 5 and footnote 1). -/
def IsMaxSupportLPSol {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (X : Instance τ ar) (𝔸 : RelStruct τ ar A) (w : Fin X.n → A → ℚ)
    (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ) : Prop :=
  IsLPSol X 𝔸 w p ∧
    ∀ (w' : Fin X.n → A → ℚ) (p' : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ),
      IsLPSol X 𝔸 w' p' →
        (∀ i a, w' i a ≠ 0 → w i a ≠ 0) ∧ (∀ j y, p' j y ≠ 0 → p j y ≠ 0)

/-- The BLP+Affine algorithm (Figure 1, p. 6) accepts `X`: `LP_ℚ(X, 𝔸)` has a maximal-support
(relative interior) solution `(w, p)`, and the refined lattice `Aff'_ℤ(X, 𝔸)`, i.e. the
solutions `(r, q)` of `Aff_ℤ(X, 𝔸)` with `r_i(a) = 0` whenever `w_i(a) = 0` and
`q_j(y) = 0` whenever `p_j(y) = 0`, is nonempty. The algorithm does not depend on `𝔹`. -/
def Accepts {τ : Type} {ar : τ → ℕ} {A : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (X : Instance τ ar) : Prop :=
  ∃ (w : Fin X.n → A → ℚ) (p : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℚ),
    IsMaxSupportLPSol X 𝔸 w p ∧
    ∃ (r : Fin X.n → A → ℤ) (q : (j : Fin X.m) → (Fin (ar (X.sym j)) → A) → ℤ),
      IsAffSol X 𝔸 r q ∧ (∀ i a, w i a = 0 → r i a = 0) ∧ (∀ j y, p j y = 0 → q j y = 0)

/-- Definition 1 (p. 6): the BLP+Affine algorithm correctly solves `PCSP-Decision(𝔸, 𝔹)` if it
accepts every instance satisfiable in `𝔸` and rejects every instance unsatisfiable in `𝔹`. -/
def CorrectlySolves {τ : Type} {ar : τ → ℕ} {A B : Type} [Fintype A] [DecidableEq A]
    (𝔸 : RelStruct τ ar A) (𝔹 : RelStruct τ ar B) : Prop :=
  ∀ X : Instance τ ar, (SatIn X 𝔸 → Accepts 𝔸 X) ∧ (Accepts 𝔸 X → SatIn X 𝔹)

end PCSPBLPAff.Symmetric


