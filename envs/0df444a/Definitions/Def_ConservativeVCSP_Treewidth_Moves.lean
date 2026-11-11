-- Prove2me | Definitions.Def_ConservativeVCSP_Treewidth_Moves
-- name    : ConservativeVCSP_Treewidth_Moves
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T21:46:49.581111+00:00
-- url     : https://prove2.me/theorems/36132496-0eb4-4860-83ae-b72f7faacbac
-- title:
--   Restrictions, domination, interaction, moves, expressing cost functions on subsets, soft lists and expressive sets
-- statement:
--   Let $B\subseteq D$ be nonempty. A unary $h$ is a **restriction to $B$** if for some $c\in\mathbb Q$, $h=c$ on $B$ and $h>c$ outside $B$ (possibly $\infty$). $\Gamma$ **expresses all finite-valued cost functions on $B$** if every $f:B^r\to\mathbb Q_{\ge0}$ ($r\ge1$) agrees on $B^r$ with a finite-valued $g\in\mathrm{pow}(\Gamma)$ up to an additive constant ($r=1$: unary). $a$ **dominates** $b$ if $h(a)\le h(b)$ for every finite-valued unary $h\in\mathrm{pow}(\Gamma)$. Distinct $a,b$ **interact** if neither dominates the other and there are distinct $c,d$, neither dominating the other, and a finite-valued binary $f\in\mathrm{pow}(\Gamma)$ with
--   $$f(a,c)-f(b,c)\neq f(a,d)-f(b,d).$$
--   A binary $g$ is a **move** from $(a,b)$ to $(c,d)$ ($a\ne b$, $c\ne d$) if $g(a,c)=g(b,d)<g(a,d)=g(b,c)$; $(a,b)\rightsquigarrow(c,d)$ means a finite-valued such move lies in $\mathrm{pow}(\Gamma)$, $\{a,b\}\rightsquigarrow\{c,d\}$ means a move to $(c,d)$ or to $(d,c)$, and a **reversing move** on $\{a,b\}$ is a move from $(a,b)$ to $(b,a)$. The **soft list** $h_S$ is $0$ on $S$ and $1$ off $S$; $\Gamma$ expresses all soft lists on $B$ if for every nonempty $S\subseteq B$ some finite-valued unary $g\in\mathrm{pow}(\Gamma)$ equals $h_S+c$ on $B$. $D'$ is **expressive** if it is pairwise interacting and $\Gamma$ expresses all soft lists on $D'$. Finally $\bar x_S\cdot\bar y_T$ agrees with $\bar x$ on $S$ and with $\bar y$ on $T=[m]\setminus S$.
--
--   **Formalization Note** The interaction inequality is stored as $f(a,c)+f(b,d)\ne f(a,d)+f(b,c)$, exact for finite values. `ExpressesOn Γ S f` is the common shape "finite-valued $g\in\mathrm{pow}(\Gamma)$ with $g=f+c$ on $S_1\times\cdots\times S_r$".
-- source:
--   Greilhuber, Marx, Osipov, Piecyk, Rzążewski, Živný, Tight Algorithms for Conservative Finite-Valued CSPs Parameterized by Treewidth, STOC 2027 submission (manuscript sha256 e3f9968e…), pp. 19–21, Definitions 4.1, 4.2, 4.4, 2.4, 2.6; p. 24, Definition 5.1; p. 30, Definition 2.11; p. 31 (x̄_S · ȳ_T)

import Definitions.Def_ConservativeVCSP_Treewidth_Pow

set_option autoImplicit false

namespace ConservativeVCSP.Treewidth

variable {D : Type} [Fintype D]

/-- `h` is a restriction to `B` (Definition 4.1, p. 19): for some `c ∈ ℚ`, `h(d) = c` on `B` and
`h(d) > c` outside `B` (values outside `B` may be `∞`). -/
def IsRestriction (h : D → WithTop ℚ≥0) (B : Set D) : Prop :=
  ∃ c : ℚ, (∀ d ∈ B, toQ (h d) = (c : WithTop ℚ)) ∧ ∀ d ∉ B, (c : WithTop ℚ) < toQ (h d)

/-- `Γ` expresses a restriction to the nonempty set `B` (Definition 4.1). -/
def ExpressesRestriction (Γ : Set (CostFn D)) (B : Set D) : Prop :=
  B.Nonempty ∧ ∃ h : D → WithTop ℚ≥0, IsRestriction h B ∧ InPow Γ (unary h)

/-- `Γ` expresses `f : S₁ × ⋯ × S_r → ℚ≥0` up to a constant: some finite-valued `g ∈ pow(Γ)` of
arity `r` and `c ∈ ℚ` have `g(x̄) = f(x̄) + c` for all `x̄ ∈ S₁ × ⋯ × S_r`
(the conclusion shape of Definition 4.2, Lemma 4.8 and Corollary 6.13). -/
def ExpressesOn (Γ : Set (CostFn D)) {r : ℕ} (S : Fin r → Set D)
    (f : ((i : Fin r) → S i) → ℚ≥0) : Prop :=
  ∃ g : (Fin r → D) → WithTop ℚ≥0, (∀ x, g x ≠ ⊤) ∧ InPow Γ ⟨r, g⟩ ∧
    ∃ c : ℚ, ∀ x : (i : Fin r) → S i, toQ (g fun i => (x i : D)) = (((f x : ℚ) + c : ℚ) : WithTop ℚ)

/-- `Γ` expresses all finite-valued cost functions on `B` (Definition 4.2, p. 19): every
`f : B^r → ℚ≥0`, `r ≥ 1`, is a finite-valued member of `pow(Γ)` up to a constant on `B^r`. -/
def ExpressesAllFV (Γ : Set (CostFn D)) (B : Set D) : Prop :=
  ∀ r : ℕ, 1 ≤ r → ∀ f : (Fin r → B) → ℚ≥0, ExpressesOn Γ (fun _ => B) f

/-- `Γ` expresses all finite-valued unary cost functions on `B` (Definition 4.2, `r = 1`). -/
def ExpressesAllUnaryFV (Γ : Set (CostFn D)) (B : Set D) : Prop :=
  ∀ f : (Fin 1 → B) → ℚ≥0, ExpressesOn Γ (fun _ => B) f

/-- `a` dominates `b` (Definition 4.4, p. 20): `h(a) ≤ h(b)` for every finite-valued unary
`h ∈ pow(Γ)`. -/
def Dominates (Γ : Set (CostFn D)) (a b : D) : Prop :=
  ∀ h : D → WithTop ℚ≥0, (∀ d, h d ≠ ⊤) → InPow Γ (unary h) → h a ≤ h b

/-- `{c, d}` and `f` witness the interaction of `a, b` (Definition 2.4, p. 21): `a ≠ b`, neither of
`a, b` dominates the other, `c ≠ d`, neither of `c, d` dominates the other, and `f ∈ pow(Γ)` is a
finite-valued binary function with `f(a,c) − f(b,c) ≠ f(a,d) − f(b,d)`, written here, for finite
values, as `f(a,c) + f(b,d) ≠ f(a,d) + f(b,c)`. -/
def InteractionWitness (Γ : Set (CostFn D)) (a b c d : D) (f : D → D → WithTop ℚ≥0) : Prop :=
  a ≠ b ∧ ¬ Dominates Γ a b ∧ ¬ Dominates Γ b a ∧
  c ≠ d ∧ ¬ Dominates Γ c d ∧ ¬ Dominates Γ d c ∧
  (∀ x y, f x y ≠ ⊤) ∧ InPow Γ (binary f) ∧
  f a c + f b d ≠ f a d + f b c

/-- `a, b` form an interacting pair (Definition 2.4). -/
def Interacting (Γ : Set (CostFn D)) (a b : D) : Prop :=
  ∃ c d f, InteractionWitness Γ a b c d f

/-- Every pair of distinct elements of `S` interacts (Definition 2.4). -/
def PairwiseInteracting (Γ : Set (CostFn D)) (S : Set D) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Interacting Γ a b

/-- `g` is a move from `(a, b)` to `(c, d)` (Definition 2.6, p. 19), for two-element sets
`{a, b}`, `{c, d}`: `g(a,c) = g(b,d) < g(a,d) = g(b,c)`. -/
def IsMove (g : D → D → WithTop ℚ≥0) (a b c d : D) : Prop :=
  a ≠ b ∧ c ≠ d ∧ g a c = g b d ∧ g b d < g a d ∧ g a d = g b c

/-- A finite-valued move `(a, b) ⇝ (c, d)`: a finite-valued move from `(a, b)` to `(c, d)` belongs
to `pow(Γ)` (Definition 2.6). A finite-valued reversing move on `{a, b}` is `FVMove Γ a b b a`. -/
def FVMove (Γ : Set (CostFn D)) (a b c d : D) : Prop :=
  ∃ g : D → D → WithTop ℚ≥0, (∀ x y, g x y ≠ ⊤) ∧ InPow Γ (binary g) ∧ IsMove g a b c d

/-- A finite-valued move `{a, b} ⇝ {c, d}`: a finite-valued move from `(a, b)` to `(c, d)` or to
`(d, c)` belongs to `pow(Γ)` (Definition 2.6). -/
def FVSetMove (Γ : Set (CostFn D)) (a b c d : D) : Prop :=
  FVMove Γ a b c d ∨ FVMove Γ a b d c

open scoped Classical in
/-- The soft list on `S` (Definition 5.1, p. 24): value `0` on `S` and `1` outside `S`. -/
noncomputable def softList (S : Set D) (d : D) : ℚ≥0 :=
  if d ∈ S then 0 else 1

/-- `Γ` expresses all soft lists on `B` (Definition 5.1, p. 24): for every nonempty `S ⊆ B` some
finite-valued unary `g ∈ pow(Γ)` and `c ∈ ℚ` have `g(d) = h_S(d) + c` for every `d ∈ B`. -/
def ExpressesSoftListsOn (Γ : Set (CostFn D)) (B : Set D) : Prop :=
  ∀ S ⊆ B, S.Nonempty → ∃ g : D → WithTop ℚ≥0, (∀ d, g d ≠ ⊤) ∧ InPow Γ (unary g) ∧
    ∃ c : ℚ, ∀ d ∈ B, toQ (g d) = (((softList S d : ℚ) + c : ℚ) : WithTop ℚ)

/-- `D'` is expressive (Definition 2.11, p. 30): it is pairwise interacting and `Γ` expresses all
soft lists on `D'`. -/
def IsExpressive (Γ : Set (CostFn D)) (D' : Set D) : Prop :=
  PairwiseInteracting Γ D' ∧ ExpressesSoftListsOn Γ D'

/-- `x̄_S · ȳ_T` (§6.1, p. 31) for the partition `S, T = [m] \ S` of the positions: agrees with `x̄` on `S` and with `ȳ` on `T`. -/
def mixTuple {m : ℕ} (S : Finset (Fin m)) (x y : Fin m → D) : Fin m → D :=
  fun i => if i ∈ S then x i else y i

end ConservativeVCSP.Treewidth


