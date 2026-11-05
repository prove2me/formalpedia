-- Prove2me | Definitions.Def_PancakeHard_Basic
-- name    : PancakeHard_Basic
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:00:36.042075+00:00
-- url     : https://prove2.me/theorems/28136f96-821f-4a48-8160-02c67a59c8ef
-- title:
--   Stacks, flips, breakpoints $d_b$, efficient paths and the relation $S \Longrightarrow \mathbb T$
-- statement:
--   A **stack** (an input sequence) is a sequence $S=\langle x_1,\dots,x_n\rangle$ that is a permutation of $\llbracket 1;n\rrbracket=\{1,\dots,n\}$; its first element $x_1$ is the **head** (the top pancake), and the sorted stack is the **identity** $\mathcal I_n^1=\langle 1,2,\dots,n\rangle$. More generally $\mathcal I_q^p=\langle p,p+1,\dots,q\rangle$ (empty when $q<p$), $\star S$ is $S$ reversed and $p+S$ adds $p$ to every entry. The module defines:
--
--   1. The **number of breakpoints** $d_b(S)$: $S$ has a breakpoint at position $1\le r<n$ if $x_r\ne x_{r+1}-1$ and $x_r\ne x_{r+1}+1$, and at position $n$ if $x_n\ne n$.
--   2. The **flip of length $r$**, $1\le r\le n$, which reverses the first $r$ elements: $\langle x_1,\dots,x_r,x_{r+1},\dots,x_n\rangle\mapsto\langle x_r,\dots,x_1,x_{r+1},\dots,x_n\rangle$.
--   3. An **efficient flip** $S\to S'$: a flip with $d_b(S')=d_b(S)-1$; an **efficient path** from $S$ to $T$: a series of efficient flips leading from $S$ to $T$; $S$ is **efficiently sortable** if there is an efficient path from $S$ to $\mathcal I_n^1$; $S$ is a **deadlock** ($S\to\bot$) if $S\ne\mathcal I_n^1$ and no efficient flip applies.
--   4. The relation $S\Longrightarrow\mathbb T$, for a set $\mathbb T$ of sequences: (1) for each $T\in\mathbb T$ there is an efficient path from $S$ to $T$, and (2) every efficient path from $S$ to the identity goes through some $T\in\mathbb T$.
--   5. $S$ **can be sorted within $k$ flips**: some at most $k$ flips, each of a length in $\llbracket 1;n\rrbracket$, applied in order, turn $S$ into $\mathcal I_n^1$.
--
--   Every statement of the mission is phrased with these notions; the relation $\Longrightarrow$ is how the paper describes all efficient paths through a gadget at once.
--
--   **Formalization Note** Sequences are lists of natural numbers with the head first. A path is recorded by the list of the sequences it visits, so that "the path goes through $T$" means that $T$ is in the list, both endpoints included; the path with no flip is an efficient path from $S$ to $S$. The paper defines $S\Longrightarrow\mathbb T$ only for $S\ne\mathcal I_n^1$; the Lean relation is the same two conditions for every $S$. The breakpoint test is written $\neg(x_r+1=x_{r+1}\lor x_{r+1}+1=x_r)$ to avoid natural-number subtraction.
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §2, pp.2–3 (sequences, breakpoints, flips, efficient flips and paths, deadlocks, the relation ⟹), §1 p.2 (MIN-SBPR)

import Mathlib

set_option autoImplicit false

namespace PancakeHard

/-- The interval sequence `𝓘^p_q = ⟨p, p+1, …, q⟩` (Bulteau, Fertin, Rusu, *Pancake Flipping Is
Hard*, arXiv:1111.0434v2, §2, p.3); it is empty when `q < p`, like `⟦p ; q⟧` (p.2).

**Formalization Note** `q + 1 - p` is truncated subtraction in `ℕ`; it is `0` exactly when
`q < p`, which gives the empty sequence. -/
def interval (p q : ℕ) : List ℕ := List.range' p (q + 1 - p)

/-- The identity permutation `𝓘¹ₙ = ⟨1, 2, …, n⟩` (arXiv:1111.0434v2, §2, p.3): the sorted stack,
smallest pancake on top. -/
def identity (n : ℕ) : List ℕ := interval 1 n

/-- `S` is a **stack** (an input sequence of the paper): a permutation of `⟦1 ; n⟧` where `n` is the
length of `S` (arXiv:1111.0434v2, §2, p.2: "Input sequences are permutations of ⟦1 ; n⟧ … there
cannot be duplicates").

**Formalization Note** A sequence `S = ⟨x₁, …, xₙ⟩` is the list `[x₁, …, xₙ]`; its first entry is
the **head element** `x₁` (the top pancake). -/
def IsStack (S : List ℕ) : Prop := S.Perm (identity S.length)

instance (S : List ℕ) : Decidable (IsStack S) := by
  unfold IsStack; infer_instance

/-- `p + S = ⟨p + x₁, …, p + x_k⟩` (arXiv:1111.0434v2, §2, p.3). -/
def shift (p : ℕ) (S : List ℕ) : List ℕ := S.map (p + ·)

/-- The **number of breakpoints** `d_b(S)` (arXiv:1111.0434v2, §2, p.2): "Sequence S has a
breakpoint at position r, 1 ≤ r < n if x_r ≠ x_{r+1} − 1 and x_r ≠ x_{r+1} + 1. It has a breakpoint
at position n if x_n ≠ n."

**Formalization Note** The test at `1 ≤ r < n` is written `¬(x_r + 1 = x_{r+1} ∨ x_{r+1} + 1 = x_r)`,
which is the page's condition without natural-number subtraction. The empty sequence (`n = 0`) has no
position and `0` breakpoints. `x₁ ≠ 1` is not a breakpoint (p.3). -/
def breakpoints (S : List ℕ) : ℕ :=
  (S.zip S.tail).countP (fun xy => !(xy.1 + 1 == xy.2 || xy.2 + 1 == xy.1)) +
    (match S.getLast? with
     | none => 0
     | some x => if x = S.length then 0 else 1)

/-- The **flip of length `r`** (arXiv:1111.0434v2, §2, p.3): reverse the `r` first elements,
`⟨x₁, …, x_r, x_{r+1}, …, xₙ⟩ ↦ ⟨x_r, …, x₁, x_{r+1}, …, xₙ⟩`.

**Formalization Note** The function is total; only lengths `1 ≤ r ≤ n` are flips of the paper,
and `IsFlip` imposes that range. -/
def flip (r : ℕ) (S : List ℕ) : List ℕ := (S.take r).reverse ++ S.drop r

/-- `S'` is obtained from `S` by one flip of a length `1 ≤ r ≤ n` (arXiv:1111.0434v2, p.3). -/
def IsFlip (S S' : List ℕ) : Prop := ∃ r : ℕ, 1 ≤ r ∧ r ≤ S.length ∧ S' = flip r S

/-- An **efficient flip** `S → S'` (arXiv:1111.0434v2, p.3): a flip with `d_b(S') = d_b(S) − 1`.

**Formalization Note** Written `d_b(S') + 1 = d_b(S)` to avoid truncated subtraction. -/
def EfficientFlip (S S' : List ℕ) : Prop := IsFlip S S' ∧ breakpoints S' + 1 = breakpoints S

/-- `π` is an **efficient path from `S` to `T`** (arXiv:1111.0434v2, p.3: "We call path a series of
flips. A path is efficient if each flip is efficient in the series").

**Formalization Note** A path is recorded by the list of the sequences it visits,
`π = [S₀, S₁, …, S_j]` with `S₀ = S`, `S_j = T` and `S_{i} → S_{i+1}` an efficient flip for every
`i`, so that "the path goes through `T`" can be said (`T ∈ π`; both endpoints count). The path with no
flip, `π = [S]`, is an efficient path from `S` to `S`. -/
def IsEfficientPath (π : List (List ℕ)) (S T : List ℕ) : Prop :=
  π.head? = some S ∧ π.getLast? = some T ∧ π.IsChain EfficientFlip

/-- `S` is **efficiently sortable** (arXiv:1111.0434v2, p.3): there is an efficient path from `S` to
the identity permutation `𝓘¹ₙ`, `n` the length of `S`. -/
def EfficientlySortable (S : List ℕ) : Prop :=
  ∃ π : List (List ℕ), IsEfficientPath π S (identity S.length)

/-- `S` is a **deadlock**, `S → ⊥` (arXiv:1111.0434v2, p.3): "A sequence of size n, different from
the identity, is a deadlock if it yields no efficient flip". -/
def IsDeadlock (S : List ℕ) : Prop := S ≠ identity S.length ∧ ∀ S' : List ℕ, ¬ EfficientFlip S S'

/-- The relation **`S ⟹ 𝕋`** (arXiv:1111.0434v2, p.3): "We write S ⟹ 𝕋 if both following
conditions are satisfied: 1. for each T ∈ 𝕋, there exists an efficient path from S to T. 2. for each
efficient path from S to the identity, there exists a sequence T ∈ 𝕋 such that the path goes
through T."

**Formalization Note** The paper defines `S ⟹ 𝕋` only for `S` different from the identity; the
definition below is the same two conditions for every `S` (at `S = 𝓘¹ₙ` the path `[S]` counts).
"Goes through `T`" includes the two endpoints of the path. `S ⟹ T` for a single sequence is
`LeadsTo S {T}`. -/
def LeadsTo (S : List ℕ) (𝕋 : Set (List ℕ)) : Prop :=
  (∀ T ∈ 𝕋, ∃ π : List (List ℕ), IsEfficientPath π S T) ∧
  (∀ π : List (List ℕ), IsEfficientPath π S (identity S.length) → ∃ T ∈ 𝕋, T ∈ π)

/-- `S` **can be sorted within `k` flips**: some list of at most `k` flip lengths, each in
`⟦1 ; n⟧`, applied in order to `S`, gives the identity `𝓘¹ₙ` (arXiv:1111.0434v2, §1, p.2, MIN-SBPR,
and p.3 "it can be sorted in d_b(S) flips").

**Formalization Note** The flips are applied left to right (`List.foldl`). "Within `k`" is "at most
`k`"; a flip of length `1` changes nothing, so at most `k` and exactly `k` flips agree when `n ≥ 1`. -/
def SortsWithin (S : List ℕ) (k : ℕ) : Prop :=
  ∃ rs : List ℕ, (∀ r ∈ rs, 1 ≤ r ∧ r ≤ S.length) ∧ rs.length ≤ k ∧
    rs.foldl (fun T r => flip r T) S = identity S.length

end PancakeHard


