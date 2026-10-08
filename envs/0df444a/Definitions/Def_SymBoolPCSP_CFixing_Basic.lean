-- Prove2me | Definitions.Def_SymBoolPCSP_CFixing_Basic
-- name    : SymBoolPCSP_CFixing_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T02:28:13.577164+00:00
-- url     : https://prove2.me/theorems/a248544d-daee-4f75-b907-2a9fd64014b9
-- title:
--   Boolean promise relations: Ham_k(S), f(P), flip_S, folded/idempotent/non-degenerate families, Par/Maj/AT, C-fixing (Defs 2.1–2.14, 4.1)
-- statement:
--   This file fixes the vocabulary of §2 and §4 of Brakensiek–Guruswami for the Boolean domain $\{0,1\}$.
--
--   **Vectors and relations.** For $x \in \{0,1\}^k$ the *Hamming weight* $|x|$ is the number of coordinates equal to $1$, and for $S \subseteq \mathbb{Z}_{\ge 0}$
--   $$\mathrm{Ham}_k(S) = \{x \in \{0,1\}^k : |x| \in S\}.$$
--   $\bar x$ is the coordinate-wise negation of $x$, and $\neg Q = \{\bar x : x \in Q\}$. For $S \subseteq [L]$, $e_S \in \{0,1\}^L$ is the indicator vector of $S$ and $e_i = e_{\{i\}}$; $\mathrm{flip}_S(P) = \{y : y \oplus e_S \in P\}$. A relation $P \subseteq \{0,1\}^k$ is *symmetric* if it is closed under every permutation of its coordinates (Definition 2.14).
--
--   **Polymorphisms.** A function $f : \{0,1\}^L \to \{0,1\}$ is a polymorphism of the promise relation $(P, Q)$ if for all $x^{(1)}, \dots, x^{(L)} \in P$ the tuple $\big(f(x^{(1)}_1, \dots, x^{(L)}_1), \dots, f(x^{(1)}_k, \dots, x^{(L)}_k)\big)$ lies in $Q$ (Definition 2.4). The set of all such tuples is $f(P)$ (Definition 2.7), so $f \in \mathrm{Pol}(P,Q)$ iff $f(P) \subseteq Q$. For a family $\Gamma$ the polymorphisms are those of every member.
--
--   **Properties of functions.** $f$ is *folded* if $f(x) = \neg f(\bar x)$ for all $x$ (Definition 2.6); *idempotent* if $f(0,\dots,0) = 0$ and $f(1,\dots,1) = 1$ (§2.3); *non-degenerate* if $f(0,\dots,0) \ne f(1,\dots,1)$ (Definition 2.11); and *$C$-fixing* if there is $S \subseteq [L]$ with $|S| \le C$ such that every $x$ vanishing on $S$ has $f(x) = f(0,\dots,0)$ (Definition 2.8). A family is folded (idempotent, non-degenerate) if all of its polymorphisms are.
--
--   **The three function families** (p. 10): $\mathrm{Par}_L(x) = x_1 \oplus \dots \oplus x_L$; $\mathrm{Maj}_L(x) = 1$ iff $\sum_i x_i > L/2$; $\mathrm{AT}_L(x) = 1$ iff $\sum_{i=1}^L (-1)^{i-1} x_i > 0$. The anti-functions are their negations. $\mathrm{AT}(P) = \bigcup_{L \text{ odd}} \mathrm{AT}_L(P)$ and $\mathrm{Maj}(P) = \bigcup_{L \text{ odd}} \mathrm{Maj}_L(P)$.
--
--   **Families.** $\Gamma' = \{(P,Q)\}$ is a *relaxation* of $\Gamma$ if $\mathrm{Pol}(\Gamma) \subseteq \mathrm{Pol}(P,Q)$ (Definition 4.1). $\Gamma \cup \{\text{SET-ZERO}, \text{SET-ONE}\}$ adds the unary promise relations $(\{(0)\},\{(0)\})$ and $(\{(1)\},\{(1)\})$, and $\neg\Gamma = ((P_i, \neg Q_i))$ (p. 11).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note** $\{0,1\}$ is `Bool` with `false` $= 0$. A family $\Gamma = \{(P_R, Q_R)\}$ is a pair of structures `𝔸 𝔹 : RelStruct τ ar Bool` from the published `PCSPBLPAff_Symmetric_Setting`, with $P_R$ = `𝔸.rel R` and $Q_R$ = `𝔹.rel R`; it is finite when `τ` is a `Fintype` and a promise family when $P_R \subseteq Q_R$ (`IsPromiseFamily`). `IsPolymorphism` from that file is Definition 2.4 for the family; `PolOf P Q f` is the same notion for one pair. Coordinates are `Fin L`, so the paper's $(-1)^{i-1}$ in $\mathrm{AT}_L$ becomes $(-1)^{i}$ for the 0-based index. $\mathrm{Par}_L$ is written as "$|x|$ is odd", which equals $x_1 \oplus \dots \oplus x_L$. Family-level properties quantify over polymorphisms of every arity $L \ge 0$; a folded, idempotent or non-degenerate family has no nullary polymorphisms (a nullary polymorphism with value $c$ would make the unary constant $c$ a polymorphism too), so these three notions agree with the paper's reading over arities $L \ge 1$. `IsRelaxation` treats a single pair $\Gamma' = \{(P,Q)\}$, the only form the paper uses (Lemmas 4.5, 4.7, 4.12). `IsCFixing` is stated for every function; the paper applies it to folded polymorphisms (Definition 2.8). The anti-functions are written as negations in the statements, e.g. `!AT L x`. SET-ZERO and SET-ONE are the new symbols `inr false` and `inr true` of the signature `τ ⊕ Bool`.
-- source:
--   J. Brakensiek, V. Guruswami, Promise Constraint Satisfaction: Algebraic Structure and a Symmetric Boolean Dichotomy, arXiv:1704.01937v2, pp. 8–12 and 16, 17, 19, Definitions 2.1, 2.4, 2.6, 2.7, 2.8, 2.11, 2.14, §2.3, Definition 4.1, flip_S (p. 16), AT(P) (p. 17), Maj(P) (p. 19)

import Mathlib
import Definitions.Def_PCSPBLPAff_Symmetric_Setting

namespace SymBoolPCSP.CFixing

open PCSPBLPAff.Symmetric

/-! ### Boolean relations and functions (§2, pp. 8–12; §4.1, p. 16)

The Boolean domain `{0, 1}` is `Bool` (`false` = 0, `true` = 1). Coordinates are indexed by
`Fin k` / `Fin L`, so the paper's 1-based index `i ∈ [L]` is `⟨i - 1, _⟩`. -/

/-- The Hamming weight `|x|`: the number of coordinates of `x` equal to `1` (p. 2). -/
def hw {k : ℕ} (x : Fin k → Bool) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card

/-- `Ham_k(S) = {x ∈ {0,1}^k : |x| ∈ S}` (p. 12). -/
def Ham (k : ℕ) (S : Set ℕ) : Set (Fin k → Bool) :=
  {x | hw x ∈ S}

/-- Coordinate-wise negation `x̄` of a Boolean vector. -/
def neg {k : ℕ} (x : Fin k → Bool) : Fin k → Bool :=
  fun i => !x i

/-- A relation `P ⊆ {0,1}^k` is symmetric if it is closed under every permutation of the
coordinates (Definition 2.14, p. 12). -/
def IsSymmetricRel {k : ℕ} (P : Set (Fin k → Bool)) : Prop :=
  ∀ x ∈ P, ∀ σ : Equiv.Perm (Fin k), x ∘ σ ∈ P

/-- `f : {0,1}^L → {0,1}` is a polymorphism of the single promise relation `(P, Q)` of arity
`k` (Definition 2.4, p. 9): whenever the `L` rows `M l` of an `L × k` matrix lie in `P`, the
`k`-tuple obtained by applying `f` to each column lies in `Q`. Same matrix shape as
`PCSPBLPAff.Symmetric.IsPolymorphism`. -/
def PolOf {k L : ℕ} (P Q : Set (Fin k → Bool)) (f : (Fin L → Bool) → Bool) : Prop :=
  ∀ M : Fin L → Fin k → Bool, (∀ l, M l ∈ P) → (fun c => f (fun l => M l c)) ∈ Q

/-- `f(P)` (Definition 2.7, p. 9): the set of all `k`-tuples `x` with
`x_i = f(x^{(1)}_i, …, x^{(L)}_i)` for some `x^{(1)}, …, x^{(L)} ∈ P`. -/
def image {k L : ℕ} (f : (Fin L → Bool) → Bool) (P : Set (Fin k → Bool)) :
    Set (Fin k → Bool) :=
  {y | ∃ M : Fin L → Fin k → Bool, (∀ l, M l ∈ P) ∧ y = fun c => f (fun l => M l c)}

/-- `¬Q = {x̄ : x ∈ Q}` (p. 11). -/
def negRel {k : ℕ} (Q : Set (Fin k → Bool)) : Set (Fin k → Bool) :=
  neg '' Q

/-- The indicator vector `e_S ∈ {0,1}^L` of `S ⊆ [L]`: `(e_S)_i = 1` iff `i ∈ S` (p. 16).
The unit vector `e_i` is `indicator {i}`. -/
def indicator {L : ℕ} (S : Finset (Fin L)) : Fin L → Bool :=
  fun i => decide (i ∈ S)

/-- `flip_S(P) = {y ∈ {0,1}^k : y ⊕ e_S ∈ P}` (p. 16). -/
def flipRel {k : ℕ} (S : Finset (Fin k)) (P : Set (Fin k → Bool)) : Set (Fin k → Bool) :=
  {y | (fun i => xor (y i) (indicator S i)) ∈ P}

/-- `f` is folded: `f(x) = ¬f(x̄)` for all `x` (Definition 2.6, p. 9). -/
def IsFolded {L : ℕ} (f : (Fin L → Bool) → Bool) : Prop :=
  ∀ x, f x = !f (neg x)

/-- `f` is idempotent: `f(0, …, 0) = 0` and `f(1, …, 1) = 1` (§2.3, p. 10). -/
def IsIdempotent {L : ℕ} (f : (Fin L → Bool) → Bool) : Prop :=
  f (fun _ => false) = false ∧ f (fun _ => true) = true

/-- `f` is non-degenerate: `f(0, …, 0) ≠ f(1, …, 1)` (Definition 2.11, p. 11). -/
def IsNonDegenerate {L : ℕ} (f : (Fin L → Bool) → Bool) : Prop :=
  f (fun _ => false) ≠ f (fun _ => true)

/-- `f` is `C`-fixing (Definition 2.8, p. 10): there is `S ⊆ [L]` with `|S| ≤ C` such that every
`x` vanishing on `S` has `f(x) = f(0, …, 0)`. -/
def IsCFixing (C : ℕ) {L : ℕ} (f : (Fin L → Bool) → Bool) : Prop :=
  ∃ S : Finset (Fin L), S.card ≤ C ∧
    ∀ x : Fin L → Bool, (∀ i ∈ S, x i = false) → f x = f (fun _ => false)

/-- The parity function `Par_L(x) = x_1 ⊕ ⋯ ⊕ x_L`, i.e. `1` iff `|x|` is odd (p. 10). -/
def Par (L : ℕ) (x : Fin L → Bool) : Bool :=
  decide (hw x % 2 = 1)

/-- The majority function `Maj_L(x) = 1` iff `Σ x_i > L/2`, i.e. `2|x| > L` (p. 10). -/
def Maj (L : ℕ) (x : Fin L → Bool) : Bool :=
  decide (L < 2 * hw x)

/-- The alternating-threshold function `AT_L(x) = 1` iff `Σ_{i=1}^{L} (−1)^{i−1} x_i > 0`
(p. 10). With 0-based indices `i : Fin L`, the sign of coordinate `i` is `(−1)^{i.val}`, so the
first coordinate counts positively. -/
def AT (L : ℕ) (x : Fin L → Bool) : Bool :=
  decide (0 < ∑ i : Fin L, (-1 : ℤ) ^ (i : ℕ) * (if x i then 1 else 0))

/-- `AT(P) = ⋃_{L odd} AT_L(P)` (proof of Lemma 4.5, p. 17). -/
def ATImage {k : ℕ} (P : Set (Fin k → Bool)) : Set (Fin k → Bool) :=
  {y | ∃ L : ℕ, Odd L ∧ y ∈ image (AT L) P}

/-- `Maj(P) = ⋃_{L odd} Maj_L(P)` (proof of Lemma 4.7, p. 19). -/
def MajImage {k : ℕ} (P : Set (Fin k → Bool)) : Set (Fin k → Bool) :=
  {y | ∃ L : ℕ, Odd L ∧ y ∈ image (Maj L) P}

/-! ### Families of Boolean promise relations

A family `Γ = {(P_R, Q_R) : R ∈ τ}` is a pair of relational structures `𝔸 𝔹 : RelStruct τ ar Bool`
on the same signature, with `P_R = 𝔸.rel R`, `Q_R = 𝔹.rel R`; it is finite when `τ` is a
`Fintype`, and a promise family when `𝔸.rel R ⊆ 𝔹.rel R` for every `R` (Definitions 2.1–2.2).
`IsPolymorphism 𝔸 𝔹 f` is Definition 2.4 for the family. -/

/-- Every `(P_R, Q_R)` is a promise relation: `P_R ⊆ Q_R` (Definition 2.1). -/
def IsPromiseFamily {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) : Prop :=
  ∀ R, 𝔸.rel R ⊆ 𝔹.rel R

/-- The family is symmetric: every `P_R` and every `Q_R` is symmetric (Definition 2.14). -/
def IsSymmetricFamily {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) : Prop :=
  ∀ R, IsSymmetricRel (𝔸.rel R) ∧ IsSymmetricRel (𝔹.rel R)

/-- The family is folded: all of its polymorphisms (of every arity) are folded
(Definition 2.6). -/
def IsFoldedFamily {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) : Prop :=
  ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsFolded f

/-- The family is idempotent: all of its polymorphisms are idempotent (§2.3). -/
def IsIdempotentFamily {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) : Prop :=
  ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsIdempotent f

/-- The family is non-degenerate: all of its polymorphisms are non-degenerate
(Definition 2.11). -/
def IsNonDegenerateFamily {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) : Prop :=
  ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → IsNonDegenerate f

/-- The single promise relation `Γ′ = {(P, Q)}` is a relaxation of `Γ`:
`Pol(Γ) ⊆ Pol(Γ′)` (Definition 4.1, p. 16). -/
def IsRelaxation {τ : Type} {ar : τ → ℕ} (𝔸 𝔹 : RelStruct τ ar Bool) {k : ℕ}
    (P Q : Set (Fin k → Bool)) : Prop :=
  ∀ (L : ℕ) (f : (Fin L → Bool) → Bool), IsPolymorphism 𝔸 𝔹 f → PolOf P Q f

/-- Arities of `Γ ∪ {SET-ZERO, SET-ONE}`: the old symbols keep their arity, the two new
symbols `inr false` (SET-ZERO) and `inr true` (SET-ONE) are unary. -/
def arConst {τ : Type} (ar : τ → ℕ) : τ ⊕ Bool → ℕ :=
  Sum.elim ar (fun _ => 1)

/-- One side of `Γ ∪ {SET-ZERO, SET-ONE}` (p. 11): the relations of `𝔸`, together with the unary
relations `{(0)}` (symbol `inr false`) and `{(1)}` (symbol `inr true`). Applied to both `𝔸` and
`𝔹`, this adds the promise relations `SET-ZERO = ({(0)}, {(0)})` and
`SET-ONE = ({(1)}, {(1)})`. -/
def withConsts {τ : Type} {ar : τ → ℕ} (𝔸 : RelStruct τ ar Bool) :
    RelStruct (τ ⊕ Bool) (arConst ar) Bool where
  rel := fun R => match R with
    | Sum.inl R => 𝔸.rel R
    | Sum.inr b => {fun _ => b}

/-- The structure of the negated relations `¬Q_R` (p. 11); `¬Γ = ((P_R, ¬Q_R))` is the pair
`(𝔸, negStruct 𝔹)`. -/
def negStruct {τ : Type} {ar : τ → ℕ} (𝔹 : RelStruct τ ar Bool) : RelStruct τ ar Bool where
  rel := fun R => negRel (𝔹.rel R)

end SymBoolPCSP.CFixing


