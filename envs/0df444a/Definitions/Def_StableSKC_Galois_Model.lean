-- Prove2me | Definitions.Def_StableSKC_Galois_Model
-- name    : StableSKC_Galois_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:18:47.154659+00:00
-- url     : https://prove2.me/theorems/9bdd1ae8-5b02-4a9e-99ff-e3c304efeba8
-- title:
--   Definitions 1.1–1.3, pp. 3–4, and §3.2–3.3, pp. 9–11 — knockout seedings, the meeting round, stable SKCs, the degree d on GF(2^k), and T(z)
-- statement:
--   This file fixes the objects of Lambers, Pendavingh and Spieksma's construction of a stable serial knockout competition.
--
--   **Knockout tournaments.** Let $n = 2^k$. A balanced knockout tournament $T$ on a set $P$ of $n$ players is given by its *seeding*: a bijection from the leaf positions $0, 1, \dots, 2^k - 1$ of a complete binary tree of depth $k$, read from left to right, to the players. In round $1$ the players at leaves $2j$ and $2j+1$ play each other, in round $2$ the winners of adjacent round-$1$ matches play each other, and so on; round $k$ is the final.
--
--   **The meeting round (Definition 1.1).** For players $x, x'$ and a round $i \in \{1, \dots, k\}$, write $v_T(x, x') = i$ if $x$ and $x'$ can meet in round $i$ of $T$, i.e. they meet there if both win all their earlier matches. In terms of leaf positions $p, p'$ of $x, x'$, this means
--   $$\lfloor p / 2^i \rfloor = \lfloor p' / 2^i \rfloor \quad\text{and}\quad \lfloor p / 2^{i-1} \rfloor \ne \lfloor p' / 2^{i-1} \rfloor,$$
--   that is, the two leaves lie in the same block of $2^i$ consecutive leaves but in different blocks of $2^{i-1}$ leaves.
--
--   **Stability (Definition 1.2).** For a finite family $\mathcal T$ of knockout tournaments on the same players, $\#\{T \in \mathcal T : v_T(x, x') = i\}$ counts the members of the family in which $x$ and $x'$ can meet in round $i$. The family is *stable in round $i$* if there is a number $c_i$ such that
--   $$\#\{T \in \mathcal T : v_T(x, x') = i\} = c_i$$
--   for all pairs of distinct players $x, x'$, and *stable* if it is stable in every round $i = 1, \dots, k$.
--
--   **Stable SKC (Definition 1.3).** A *serial knockout competition* (SKC) for $n = 2^k$ players consists of $n - 1 = 2^k - 1$ knockout tournaments; a stable SKC is such a family that is stable.
--
--   **The degree on $\mathrm{GF}(2^k)$ (§3.2).** Fix an irreducible polynomial $q \in \mathbb Z_2[X]$ of degree $k$ and a root $\alpha$ of $q$, so that $\mathrm{GF}(2^k) \cong \mathbb Z_2[X]/(q)$ and every $x \in \mathrm{GF}(2^k)$ is uniquely $x = \sum_{i=0}^{k-1} x_i \alpha^i$ with $x_i \in \mathbb Z_2$. The degree of $x$ is
--   $$d(x) = \max\{i : x_i \ne 0\}.$$
--
--   **The relabelled tournament $T(z)$ (§3.3).** For a knockout tournament $T$ whose players are the elements of $\mathrm{GF}(2^k)$ and a nonzero $z \in \mathrm{GF}(2^k)$, $T(z)$ is the tournament obtained from $T$ by replacing each player $x$ with $zx$.
--
--   These definitions are the vocabulary of the paper's main result, Theorem 3.1, which shows that the $2^k - 1$ tournaments $T(z)$, $z \ne 0$, form a stable SKC.
--
--   **Formalization Note** A tournament is a seeding `Seeding k P := Fin (2 ^ k) ≃ P` (leaf position to player), and $v_T(x,x') = i$ is the predicate `CanMeetIn T x x' i`, which includes $1 \le i \le k$; it is a predicate rather than a function, so no junk value appears for $x = x'$. A family of tournaments is indexed, `𝒯 : ι → Seeding k P` with `[Fintype ι]`, and `meetCount 𝒯 x x' i` counts indices. `IsStableSKC` requires `Fintype.card ι = 2 ^ k - 1` and stability in every round $1 \le i \le k$. $\mathrm{GF}(2^k)$ with its $\alpha$ is a field `F` with a power basis `pb : PowerBasis (ZMod 2) F` (so $k$ = `pb.dim`, $\alpha$ = `pb.gen`, $x_i$ = `pb.basis.repr x i`). `deg pb 0 = 0` is a junk value (the page leaves $d(0)$ undefined); every statement of the mission uses $d$ only at nonzero arguments. `scale T z` is $T(z)$ for a unit `z : Fˣ`.
-- source:
--   Lambers, Pendavingh & Spieksma, How to Design a Stable Serial Knockout Competition, arXiv:2211.02513v1, pp. 2–5, 9, 11, Definitions 1.1–1.3, §2 (seeding, Figure 1), §3.2, §3.3

import Mathlib

namespace StableSKC.Galois

/-- A balanced knockout tournament on `2 ^ k` players of type `P`, given by its seeding
(Lambers–Pendavingh–Spieksma, p. 5): leaf position `p : Fin (2 ^ k)`, read left to right, ↦ the
player placed at that leaf. Leaves `2j` and `2j + 1` meet in round 1, adjacent round-1 winners
in round 2, and so on; round `k` is the final. -/
abbrev Seeding (k : ℕ) (P : Type*) := Fin (2 ^ k) ≃ P

/-- Definition 1.1 (p. 3), `v_T(x, x') = i`: players `x` and `x'` can meet in round `i` of the
knockout tournament `T`, `1 ≤ i ≤ k`. Their leaves lie in the same block of `2 ^ i` consecutive
leaves (the subtree whose winner plays in round `i + 1`) but in different blocks of `2 ^ (i - 1)`
leaves (the two subtrees whose winners meet in round `i`). -/
def CanMeetIn {k : ℕ} {P : Type*} (T : Seeding k P) (x x' : P) (i : ℕ) : Prop :=
  1 ≤ i ∧ i ≤ k ∧
  (T.symm x : ℕ) / 2 ^ i = (T.symm x' : ℕ) / 2 ^ i ∧
  (T.symm x : ℕ) / 2 ^ (i - 1) ≠ (T.symm x' : ℕ) / 2 ^ (i - 1)

instance {k : ℕ} {P : Type*} (T : Seeding k P) (x x' : P) (i : ℕ) :
    Decidable (CanMeetIn T x x' i) := by
  unfold CanMeetIn; infer_instance

/-- `#{T ∈ 𝒯 : v_T(x, x') = i}` for an indexed family `𝒯 : ι → Seeding k P` of knockout
tournaments: the number of indices `r` such that `x` and `x'` can meet in round `i` of `𝒯 r`. -/
def meetCount {k : ℕ} {P ι : Type*} [Fintype ι] (𝒯 : ι → Seeding k P) (x x' : P) (i : ℕ) : ℕ :=
  (Finset.univ.filter fun r => CanMeetIn (𝒯 r) x x' i).card

/-- Definition 1.2 (p. 3): the family `𝒯` is stable in round `i` if there is a number `c_i` with
`#{T ∈ 𝒯 : v_T(x, x') = i} = c_i` for all pairs of distinct players `x, x'`. -/
def StableInRound {k : ℕ} {P ι : Type*} [Fintype ι] (𝒯 : ι → Seeding k P) (i : ℕ) : Prop :=
  ∃ c : ℕ, ∀ x x' : P, x ≠ x' → meetCount 𝒯 x x' i = c

/-- Definition 1.2 (p. 3): the family `𝒯` is stable if it is stable in all rounds `i = 1, …, k`. -/
def IsStable {k : ℕ} {P ι : Type*} [Fintype ι] (𝒯 : ι → Seeding k P) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i ≤ k → StableInRound 𝒯 i

/-- Definitions 1.2 and 1.3 (pp. 3–4): a stable Serial Knockout Competition on `n = 2 ^ k`
players is a family of `n - 1 = 2 ^ k - 1` knockout tournaments that is stable. -/
def IsStableSKC {k : ℕ} {P ι : Type*} [Fintype ι] (𝒯 : ι → Seeding k P) : Prop :=
  Fintype.card ι = 2 ^ k - 1 ∧ IsStable 𝒯

/-- The degree `d(x) = max {i : x_i ≠ 0}` of an element `x = ∑_{i=0}^{k-1} x_i α^i` of
`GF(2^k)` (p. 9), where `α = pb.gen` and `x_i = pb.basis.repr x i` are the coordinates of `x` in
the power basis `1, α, …, α^(k-1)`. Junk value `0` at `x = 0` (the maximum of the empty set),
where the paper leaves `d` undefined; it is never used there. -/
noncomputable def deg {F : Type*} [Field F] [Algebra (ZMod 2) F] (pb : PowerBasis (ZMod 2) F)
    (x : F) : ℕ :=
  ((Finset.univ.filter fun i : Fin pb.dim => pb.basis.repr x i ≠ 0).image
    (fun i : Fin pb.dim => (i : ℕ))).sup id

/-- `T(z)` (p. 11): the knockout tournament obtained from `T` by replacing each player `x` with
`z x`, i.e. the player at each leaf `p` becomes `z * T p`. -/
def scale {k : ℕ} {F : Type*} [Field F] (T : Seeding k F) (z : Fˣ) : Seeding k F :=
  T.trans (Units.mulLeft z)

end StableSKC.Galois


