-- Prove2me | Definitions.Def_VAS5Reach_Supplement_MixedLPS
-- name    : VAS5Reach_Supplement_MixedLPS
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:48:39.002748+00:00
-- url     : https://prove2.me/theorems/f1f6a9d0-30e2-40e1-b82a-89dee86b706f
-- title:
--   Linear path schemes and mixed linear path schemes
-- statement:
--   A **linear path scheme** (LPS) over $\mathbb Z^d$ is an expression $\Lambda=\alpha_0\beta_1^*\alpha_1\cdots\beta_k^*\alpha_k$ in which every path $\alpha_i$ is a finite sequence of vectors of $\mathbb Z^d$ and every cycle $\beta_i$ is a nonempty such sequence. Its size is $|\Lambda|=|\alpha_0\beta_1\alpha_1\cdots\beta_k\alpha_k|$ (each cycle counted once) and its norm $\|\Lambda\|$ is the largest max norm of a vector appearing in it. It **captures** the sequences $\alpha_0\beta_1^{n_1}\alpha_1\cdots\beta_k^{n_k}\alpha_k$, $n_1,\dots,n_k\in\mathbb N$. For $X\in\{\mathbb N,\mathbb Z\}$, $s\xrightarrow{\Lambda}_X t$ holds if $\Lambda$ captures a sequence whose sum is $t-s$ and whose prefix sums, added to $s$, all lie in $X^d$.
--
--   A **mixed LPS** is $\Lambda=(\Lambda_1,X_1)\cdots(\Lambda_m,X_m)$ with $m\ge0$, LPS $\Lambda_i$ and $X_i\in\{\mathbb N,\mathbb Z\}$; $|\Lambda|=\sum_i|\Lambda_i|$ and $\|\Lambda\|=\max_i\|\Lambda_i\|$. One writes $c_0\xrightarrow{\Lambda}c_m$ if there are nonnegative vectors $c_0,\dots,c_m$ with $c_{i-1}\xrightarrow{\Lambda_i}_{X_i}c_i$ for all $i$; counter values inside a $\mathbb Z$-component may be negative. A **witness** fixes the captured sequences and the junction vectors; its length is the total number of vectors in its sequences. $\mathrm{Reach}_\Lambda=\{(s,t):s\xrightarrow{\Lambda}t\}$.
--
--   Mixed LPS are one of the two kinds of factors in the polynomial factorization of Theorem C.1.
--
--   **Formalization Note** An LPS is stored as $\alpha_0$ and the list of pairs $(\beta_i,\alpha_i)$; letters are arbitrary integer vectors. Junction vectors are vectors of natural numbers; $m=0$ gives the identity relation.
-- source:
--   Chen, Fu, Fu, Reachability in Five-Dimensional Vector Addition Systems Is PSPACE-Complete, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 'Mixed Linear Path Schemes', p.15 (PDF p.17)

import Mathlib
import Definitions.Def_VAS5Reach_supNorm

namespace VAS5Reach.Supplement

open VAS5Reach

/-- A **linear path scheme** (LPS) `Λ = α₀ β₁* α₁ ⋯ β_k* α_k` over `ℤ^d`: `head = α₀` and
`blocks = [(β₁, α₁), …, (β_k, α_k)]`, where every path `αᵢ` is a finite sequence of vectors of
`ℤ^d` and every cycle `βᵢ` is a nonempty such sequence.

Source: W. Chen, B. Fu, Y. Fu, *Reachability in Five-Dimensional Vector Addition Systems Is
PSPACE-Complete*, arXiv:2610.40012 (held version, sha256 a74d76f9…), §3 "Mixed Linear Path
Schemes", printed p. 15 (PDF p. 17): "A linear path scheme (LPS) is a regular expression
Λ = α0 β∗1 α1 · · · β∗k αk, where each path αi is a finite sequence of vectors in Zd, and each cycle
βi is a nonempty such sequence."

**Formalization Note** Letters are arbitrary vectors of `ℤ^ι` (not required to be transitions of a
given VAS), as on the page. -/
structure LPS (ι : Type) where
  /-- the first path `α₀` -/
  head : List (ι → ℤ)
  /-- the pairs `(βᵢ, αᵢ)`, `i = 1, …, k` -/
  blocks : List (List (ι → ℤ) × List (ι → ℤ))
  /-- every cycle `βᵢ` is nonempty -/
  cycle_ne : ∀ b ∈ blocks, b.1 ≠ []

namespace LPS

variable {ι : Type}

/-- `|Λ| := |α₀ β₁ α₁ ⋯ β_k α_k|`: every cycle counted once. -/
def size (Λ : LPS ι) : ℕ :=
  Λ.head.length + (Λ.blocks.map fun b => b.1.length + b.2.length).sum

/-- The vectors appearing in `Λ`, i.e. the word `α₀ β₁ α₁ ⋯ β_k α_k`. -/
def letters (Λ : LPS ι) : List (ι → ℤ) :=
  Λ.head ++ Λ.blocks.flatMap fun b => b.1 ++ b.2

/-- `∥Λ∥ := max{∥a∥ : a appears in Λ}` (max norm; `0` if no vector appears). -/
def norm [Fintype ι] (Λ : LPS ι) : ℕ :=
  (Λ.letters.map supNorm).foldr max 0

/-- The sequence `α₀ β₁^{n₁} α₁ ⋯ β_k^{n_k} α_k` for the repetition counts `n = [n₁, …, n_k]`. -/
def expand (Λ : LPS ι) (n : List ℕ) : List (ι → ℤ) :=
  Λ.head ++ (List.zipWith (fun b k => (List.replicate k b.1).flatten ++ b.2) Λ.blocks n).flatten

/-- `Λ` captures the sequence `w`: `w = α₀ β₁^{n₁} α₁ ⋯ β_k^{n_k} α_k` for some
`n₁, …, n_k ∈ ℕ`. -/
def Captures (Λ : LPS ι) (w : List (ι → ℤ)) : Prop :=
  ∃ n : List ℕ, n.length = Λ.blocks.length ∧ w = Λ.expand n

end LPS

/-- The two semantics `X ∈ {ℕ, ℤ}` of a component of a mixed LPS. -/
inductive Sem
  | N
  | Z
  deriving DecidableEq

/-- `x −Λ→_X y` witnessed by the captured sequence `w`: `Λ` captures `w`, `y = x + Σ w`, and for
`X = ℕ` every prefix sum added to `x` lies in `ℕ^d` (for `X = ℤ` there is no constraint)
(printed p. 15, PDF p. 17: "For X ∈ {N, Z}, write s −Λ→X t if Λ captures a sequence of vectors
whose sum is t − s and whose prefix sums, when added to s, all lie in X^d"). The endpoints are
nonnegative vectors, which is how components are used inside a mixed LPS. -/
def LPSStep {ι : Type} (X : Sem) (Λ : LPS ι) (x : ι → ℕ) (w : List (ι → ℤ)) (y : ι → ℕ) :
    Prop :=
  Λ.Captures w ∧ (∀ i, (y i : ℤ) = (x i : ℤ) + w.sum i) ∧
    (X = Sem.N → ∀ j ≤ w.length, ∀ i, 0 ≤ (x i : ℤ) + (w.take j).sum i)

/-- A **mixed linear path scheme** `Λ = (Λ₁, X₁) ⋯ (Λ_m, X_m)`, `m ≥ 0`, each `Λᵢ` an LPS and
`Xᵢ ∈ {ℕ, ℤ}` (printed p. 15, PDF p. 17). -/
abbrev MixedLPS (ι : Type) := List (LPS ι × Sem)

namespace MixedLPS

variable {ι : Type}

/-- `|Λ| := Σᵢ |Λᵢ|`. -/
def size (Λ : MixedLPS ι) : ℕ := (Λ.map fun c => c.1.size).sum

/-- `∥Λ∥ := maxᵢ ∥Λᵢ∥` (`0` for `m = 0`). -/
def norm [Fintype ι] (Λ : MixedLPS ι) : ℕ := (Λ.map fun c => c.1.norm).foldr max 0

/-- A witness of `x −Λ→ y`: nonnegative junction vectors `x = c₀, c₁, …, c_m = y` and, for each
component, a sequence `wᵢ` captured by `Λᵢ` with `c_{i−1} −Λᵢ→_{Xᵢ} cᵢ` along `wᵢ`; `ws` lists the
sequences `w₁, …, w_m`.

Source: arXiv:2610.40012 (held version, sha256 a74d76f9…), printed p. 15 (PDF p. 17): "We write
c0 −Λ→ cm if there exist nonnegative vectors c0, . . . , cm such that ci−1 −Λi→Xi ci for all i. The
counter values inside a Z-component may be negative. A witness w specifies the repetition counts of
all cycles and the intermediate vectors between consecutive components. […] The length |w| is the
total number of vectors in the resulting sequences."

**Formalization Note** The junction vectors are `ι → ℕ` (nonnegative by type); `m = 0` gives the
identity relation. The witness length is `Σᵢ |wᵢ|` (`witnessLength`). -/
inductive IsWitness : MixedLPS ι → (ι → ℕ) → List (List (ι → ℤ)) → (ι → ℕ) → Prop
  | nil (x : ι → ℕ) : IsWitness [] x [] x
  | cons {Λ : LPS ι} {X : Sem} {rest : MixedLPS ι} {x c y : ι → ℕ} {w : List (ι → ℤ)}
      {ws : List (List (ι → ℤ))} :
      LPSStep X Λ x w c → IsWitness rest c ws y → IsWitness ((Λ, X) :: rest) x (w :: ws) y

/-- The length `|w|` of a witness: the total number of vectors in its sequences. -/
def witnessLength (ws : List (List (ι → ℤ))) : ℕ := (ws.map List.length).sum

/-- `Reach_Λ := {(s, t) : s −Λ→ t}`. -/
def Reach (Λ : MixedLPS ι) (x y : ι → ℕ) : Prop := ∃ ws, IsWitness Λ x ws y

end MixedLPS

end VAS5Reach.Supplement


