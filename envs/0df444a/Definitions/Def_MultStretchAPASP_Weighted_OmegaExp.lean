-- Prove2me | Definitions.Def_MultStretchAPASP_Weighted_OmegaExp
-- name    : MultStretchAPASP_Weighted_OmegaExp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T07:08:59.978569+00:00
-- url     : https://prove2.me/theorems/1389fbe1-caa1-425f-9183-e6cd0cbb99eb
-- title:
--   The operational rectangular matrix multiplication exponent ω(a, b, c) on the randomized word RAM
-- statement:
--   The paper defines $\omega(a,b,c)$ as "the infimum over all $\tau>0$ such that, for every constant $\varepsilon>0$, the product $A\cdot B$ can be computed in $O(n^{\tau+\varepsilon})$ runtime", for $A$ of size $n^a\times n^b$ and $B$ of size $n^b\times n^c$; $\omega=\omega(1,1,1)$.
--
--   Here running time is measured on the randomized word RAM of `DynConnWC_Program` with the run notions of `MinKCutII_Main_Runs`. Say that $\tau$ is **achievable** for $(a,b,c)$ if for every $\varepsilon>0$ there are a deterministic program $P$ and a constant $C$ such that for every $N\ge1$ and all natural-number matrices $A\in\mathbb N^{\lceil N^a\rceil\times\lceil N^b\rceil}$, $B\in\mathbb N^{\lceil N^b\rceil\times\lceil N^c\rceil}$, given the three dimensions and then the entries row by row, $P$ halts within $C N^{\tau+\varepsilon}+C$ steps (with words of $C\lceil\log_2(\text{input length}+\text{input sum}+2+\lceil T\rceil)\rceil$ bits) and writes the entries of $A\cdot B$ row by row. Then
--   $$\omega(a,b,c)=\inf\{\tau>0 : \tau\text{ is achievable for }(a,b,c)\},\qquad \omega=\omega(1,1,1).$$
--
--   **Formalization Note.** This is the paper's operational exponent, not the algebraic (bilinear-rank) exponent of other platform definitions. Programs are deterministic because Theorem 2.14 claims a deterministic algorithm in time $n^{\omega(1,r,1)+o(1)}$. The set of achievable $\tau$ is nonempty (the schoolbook algorithm) and bounded below by $0$, so the real infimum is not the junk value of an empty set. Dimensions $n^x$ are rounded up.
-- source:
--   Saggi, Sapir, Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime, arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), p. 7, §2.4

import Mathlib
import Definitions.Def_DynConnWC_Program
import Definitions.Def_MinKCutII_Main_Runs

set_option autoImplicit false

open DynConnWC MinKCutII.Main

namespace MultStretchAPASP.Weighted

/-!
# The operational rectangular matrix multiplication exponent `ω(a, b, c)`

Saggi, Sapir, *Smallest Multiplicative Stretch for an α-APASP Below Õ(n^ω) Runtime*,
arXiv:2611.04736 (version of November 3, 2026, sha256 7cbb8123…), §2.4, p. 7: "the classical
notation of ω(a, b, c) as the infimum over all τ > 0 such that, for every constant ε > 0, the
product A·B can be computed in O(n^{τ+ε}) runtime", for `A ∈ R^{n^a × n^b}`,
`B ∈ R^{n^b × n^c}`; "We write ω = ω(1, 1, 1)".

The definition is the paper's, by running time, on the published randomized word RAM
`DynConnWC.Program` with the run notions of `MinKCutII_Main_Runs` (halting within `T` steps,
final output, deterministic programs, word size `wordSize C inp T`):

* `dimOf N x = ⌈N^x⌉`, the paper's dimension `n^x` (here the size parameter is called `N`).
* An input is `[r, s, t]` followed by the entries of `A` (`r × s`) and then of `B` (`s × t`), row
  by row (`natMatWords`); the output must be the entries of `A·B` row by row. Entries are natural
  numbers (the machine holds integers; the word size grows with the input, so every entry fits
  in a word).
* `MatMulAchieves a b c τ`: for every `ε > 0` there are a deterministic program `P` and a
  constant `C` such that for every `N ≥ 1` and all such matrices, every run of `P` halts within
  `C·N^{τ+ε} + C` steps with the exact product as output. Programs are required to be
  deterministic, as Theorem 2.14 of the paper claims a deterministic algorithm with running time
  `n^{ω(1,r,1)+o(1)}`.
* `omega3 a b c = ω(a, b, c)` is the infimum of the `τ > 0` with `MatMulAchieves a b c τ`, and
  `omega = ω(1, 1, 1)`. The set is bounded below by `0` and nonempty (the schoolbook algorithm),
  so the real infimum is a genuine infimum, not the junk value of an empty set.
-/

/-- The paper's dimension `n^x`, rounded up: `⌈N^x⌉`. -/
noncomputable def dimOf (N : ℕ) (x : ℝ) : ℕ :=
  ⌈(N : ℝ) ^ x⌉₊

/-- The entries of a natural-number matrix, row by row. -/
def natMatWords {r t : ℕ} (A : Fin r → Fin t → ℕ) : List ℕ :=
  (List.finRange r).flatMap fun i => (List.finRange t).map fun j => A i j

/-- The input of a matrix product: the three dimensions, then `A` and `B` row by row. -/
def matMulInput {r s t : ℕ} (A : Fin r → Fin s → ℕ) (B : Fin s → Fin t → ℕ) : List ℕ :=
  [r, s, t] ++ natMatWords A ++ natMatWords B

/-- The product of `⌈N^a⌉ × ⌈N^b⌉` and `⌈N^b⌉ × ⌈N^c⌉` matrices can be computed in
`O(N^{τ+ε})` time for every `ε > 0`, by deterministic programs. -/
def MatMulAchieves (a b c τ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ P : Program, IsDeterministic P ∧ ∃ C : ℕ,
    ∀ N : ℕ, 1 ≤ N →
      ∀ (A : Fin (dimOf N a) → Fin (dimOf N b) → ℕ) (B : Fin (dimOf N b) → Fin (dimOf N c) → ℕ),
        let T : ℝ := (C : ℝ) * (N : ℝ) ^ (τ + ε) + C
        let inp := matMulInput A B
        let W := wordSize C inp T
        ∀ ω : ℕ → Fin (2 ^ W),
          HaltsWithin W P inp ω T ∧
            finalOutput W P inp ω = natMatWords (fun i k => ∑ j, A i j * B j k)

/-- `ω(a, b, c)`: the infimum of the `τ > 0` with `MatMulAchieves a b c τ`. -/
noncomputable def omega3 (a b c : ℝ) : ℝ :=
  sInf {τ : ℝ | 0 < τ ∧ MatMulAchieves a b c τ}

/-- `ω = ω(1, 1, 1)`. -/
noncomputable def omega : ℝ :=
  omega3 1 1 1

end MultStretchAPASP.Weighted


