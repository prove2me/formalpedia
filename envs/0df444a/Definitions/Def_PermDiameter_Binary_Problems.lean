-- Prove2me | Definitions.Def_PermDiameter_Binary_Problems
-- name    : PermDiameter_Binary_Problems
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:10:31.420847+00:00
-- url     : https://prove2.me/theorems/794e784c-7c72-4442-a50e-a2b8bcf6bcef
-- title:
--   Binary Length and Binary Diameter as decision problems on explicitly encoded permutations ($k$ in binary)
-- statement:
--   A permutation group of degree $d$ acts on $\Omega=\{0,\dots,d-1\}$ (the paper's $[1,d]$), and a permutation $\sigma$ is written as the list $(\sigma(0),\dots,\sigma(d-1))$ of its images. Every natural number of an instance (the degree, the length of a list, the threshold $k$) is written in **binary** with a self-delimiting numeral.
--
--   **Binary Diameter.** Input: $d$, a finite set $\Sigma\subseteq\mathrm{Sym}(d)$ (as a list), and $k\in\mathbb N$ in binary. Question: does $\operatorname{diam}(\langle\Sigma\rangle,\Sigma)\le k$ hold? An instance is **symmetric** if $\Sigma=\Sigma^{-1}$.
--
--   **Binary Length.** Input: $d$, $\Sigma\subseteq\mathrm{Sym}(d)$, $g\in\mathrm{Sym}(d)$ and $k\in\mathbb N$ in binary. Question: does $\ell(g,\Sigma)\le k$ hold? The paper's input requires $g\in G=\langle\Sigma\rangle$ (`Valid`); the question is false when $g\notin G$, where $\ell=\infty$. The restriction of Theorem 4.1 asks that $G$ be **3-step nilpotent**, $\gamma_3(G)=1$ with $\gamma_0(G)=G$, $\gamma_{i+1}(G)=[\gamma_i(G),G]$, and **metabelian**, $G^{(2)}=1$.
--
--   The file also fixes the encodings of the inputs and outputs of the algorithmic lemmas: generating sets, membership queries, stabilizer tables (for every point, three lists), permutations with their degree, numbers in **unary** (where the paper bounds running time in the value of a number), and tuples of binary numbers.
--
--   **Formalization Note.** `encNat`, `encFin`, `encTable` are the published `OptimalQueuingComplexity_Restless_encNat` encodings. `encDiam` writes `d`, the list of generators (its length, then each image list) and `k`; `encLength` writes `d`, the generators, `g` and `k`. `BinaryDiameter x` is `diamOn ⟨Σ⟩ Σ ≤ k` and `BinaryLength x` is `wordLength Σ g ≤ k`, both in `ℕ∞`. `NilpotentMetabelian` uses `Subgroup.lowerCentralSeries` (indexed from `0` with $G$ itself) and `derivedSeries`.
-- source:
--   Lohrey, Thumm, Word Length and Diameter in Permutation Groups, arXiv:2609.26307 (PDF sha256 cd20cd77…28d9), p. 3 (problems Length and Diameter, binary variants), p. 9 (symmetric sets, nilpotent and metabelian groups), p. 10 (encoding of permutations)

import Mathlib
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat
import Definitions.Def_PermDiameter_Binary_WordLength

open OptimalQueuingComplexity.Restless

namespace PermDiameter.Binary

/-!
# Binary Length and Binary Diameter with explicit encodings (Lohrey–Thumm, p. 3 and p. 10)

The domain `Ω` of degree `d` is `Fin d` (the paper's `[1, d]`, shifted to start at `0`), and a
permutation `σ` is written as the list `(σ 0, …, σ (d-1))` of its images (p. 10). Every natural
number (the degree, a list length, the threshold `k`) is written in binary with the
self-delimiting numeral `encNat` (published definition `OptimalQueuingComplexity_Restless_encNat`),
so `k` is **binary** and `d` is effectively unary (it is the length of every image list).
-/

/-- A permutation of `Fin d` as the list of its images, each image a binary numeral. -/
def encPerm {d : ℕ} (σ : Equiv.Perm (Fin d)) : List Bool :=
  encTable encFin (fun i => σ i)

/-- A finite list of permutations: its length, then each permutation by `encPerm`. -/
def encPermList {d : ℕ} (L : List (Equiv.Perm (Fin d))) : List Bool :=
  encNat L.length ++ L.flatMap encPerm

/-- An instance `(Σ, k)` of **Binary Diameter**: a degree `d`, a finite set `Σ ⊆ Sym(d)` given as
a list `gens`, and a threshold `k ∈ ℕ`. -/
structure DiamInstance where
  /-- the degree -/
  d : ℕ
  /-- the generating set `Σ`, listed -/
  gens : List (Equiv.Perm (Fin d))
  /-- the threshold, written in binary -/
  k : ℕ

/-- Encoding of a Binary Diameter instance: `d`, then `Σ`, then `k` in binary. -/
def encDiam (x : DiamInstance) : List Bool :=
  encNat x.d ++ encPermList x.gens ++ encNat x.k

/-- The set `Σ` of the generators of a Binary Diameter instance. -/
def DiamInstance.genSet (x : DiamInstance) : Set (Equiv.Perm (Fin x.d)) := {a | a ∈ x.gens}

/-- **Binary Diameter** (p. 3): does `diam(G, Σ) ≤ k` hold, where `G = ⟨Σ⟩`? -/
def BinaryDiameter (x : DiamInstance) : Prop :=
  diamOn (Subgroup.closure x.genSet : Set (Equiv.Perm (Fin x.d))) x.genSet ≤ (x.k : ℕ∞)

/-- A **symmetric** instance: `Σ = Σ⁻¹` (p. 9), i.e. `Σ` is closed under inverses. -/
def DiamInstance.Symmetric (x : DiamInstance) : Prop :=
  ∀ a ∈ x.gens, a⁻¹ ∈ x.gens

/-- An instance `(Σ, g, k)` of **Binary Length**: degree `d`, generators `Σ` (listed), a target
permutation `g` and a threshold `k ∈ ℕ`. The paper's input requires `g ∈ ⟨Σ⟩`; this is the
predicate `LengthInstance.Valid`. -/
structure LengthInstance where
  /-- the degree -/
  d : ℕ
  /-- the generating set `Σ`, listed -/
  gens : List (Equiv.Perm (Fin d))
  /-- the target element -/
  g : Equiv.Perm (Fin d)
  /-- the threshold, written in binary -/
  k : ℕ

/-- Encoding of a Binary Length instance: `d`, `Σ`, `g`, then `k` in binary. -/
def encLength (x : LengthInstance) : List Bool :=
  encNat x.d ++ encPermList x.gens ++ encPerm x.g ++ encNat x.k

/-- The set `Σ` of the generators of a Binary Length instance. -/
def LengthInstance.genSet (x : LengthInstance) : Set (Equiv.Perm (Fin x.d)) := {a | a ∈ x.gens}

/-- The input condition of Length (p. 3): `g ∈ G = ⟨Σ⟩`. -/
def LengthInstance.Valid (x : LengthInstance) : Prop :=
  x.g ∈ Subgroup.closure x.genSet

/-- **Binary Length** (p. 3): does `ℓ(g, Σ) ≤ k` hold? (False when `g ∉ ⟨Σ⟩`, where `ℓ = ⊤`.) -/
def BinaryLength (x : LengthInstance) : Prop :=
  wordLength x.genSet x.g ≤ (x.k : ℕ∞)

/-- `G = ⟨Σ⟩` is **3-step nilpotent** (`γ₃(G) = 1`, with `γ₀(G) = G`, p. 9) and **metabelian**
(`G⁽²⁾ = 1`, p. 9). `Subgroup.lowerCentralSeries S` (`γ₀ = S`, `γᵢ₊₁ = [γᵢ, S]`, computed in the
ambient group) and `derivedSeries` start at index `0` with `G` itself, as the paper does. -/
def LengthInstance.NilpotentMetabelian (x : LengthInstance) : Prop :=
  (Subgroup.closure x.genSet).lowerCentralSeries 3 = ⊥ ∧
    derivedSeries (Subgroup.closure x.genSet) 2 = ⊥

/-! ## Encodings for the algorithmic lemmas -/

/-- A generating set of a permutation group of degree `d` (input of Lemma 2.3). -/
abbrev GenSet : Type := (d : ℕ) × List (Equiv.Perm (Fin d))

/-- Encoding of a generating set: `d`, then the list. -/
def encGenSet (x : GenSet) : List Bool := encNat x.1 ++ encPermList x.2

/-- A membership query (Lemma 2.3, first task): a generating set and a permutation `g`. -/
abbrev MemQuery : Type := (d : ℕ) × List (Equiv.Perm (Fin d)) × Equiv.Perm (Fin d)

/-- Encoding of a membership query: `d`, the generators, then `g`. -/
def encMemQuery (x : MemQuery) : List Bool := encNat x.1 ++ encPermList x.2.1 ++ encPerm x.2.2

/-- Output of Lemma 2.3's third task: for every point `ω ∈ Fin d`, a triple
(generators of the stabilizer, a left transversal, a right transversal). -/
abbrev StabTable : Type :=
  (d : ℕ) × (Fin d → List (Equiv.Perm (Fin d)) × List (Equiv.Perm (Fin d)) ×
    List (Equiv.Perm (Fin d)))

/-- Encoding of a stabilizer table: `d`, then the three lists of every point in order. -/
def encStabTable (x : StabTable) : List Bool :=
  encNat x.1 ++ encTable (fun T => encPermList T.1 ++ encPermList T.2.1 ++ encPermList T.2.2) x.2

/-- A permutation together with its degree (output of Lemmas 2.5 and 3.2). -/
abbrev PermWithDegree : Type := (d : ℕ) × Equiv.Perm (Fin d)

/-- Encoding of a permutation with its degree: `d`, then the image list. -/
def encPermWithDegree (x : PermWithDegree) : List Bool := encNat x.1 ++ encPerm x.2

/-- A natural number in **unary**: `n` ones, then a zero. Used where the paper measures running
time in the value of a number ("time polynomial in `d`", Lemmas 2.5 and 3.4). -/
def encUnary (n : ℕ) : List Bool := List.replicate n true ++ [false]

/-- A list of natural numbers in unary (input of Lemma 2.5). -/
def encUnaryList (L : List ℕ) : List Bool := encNat L.length ++ L.flatMap encUnary

/-- A number and a list of numbers, all in binary (output of Lemma 3.4: `r` and `s₁, …, s_d`). -/
def encNatAndList (x : ℕ × List ℕ) : List Bool :=
  encNat x.1 ++ encNat x.2.length ++ x.2.flatMap encNat

/-- Four numbers in binary (output of Lemma 3.2: `n, q, m, d_c`). -/
def encNat4 (x : ℕ × ℕ × ℕ × ℕ) : List Bool :=
  encNat x.1 ++ encNat x.2.1 ++ encNat x.2.2.1 ++ encNat x.2.2.2

end PermDiameter.Binary


