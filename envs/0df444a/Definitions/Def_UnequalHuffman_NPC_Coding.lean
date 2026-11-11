-- Prove2me | Definitions.Def_UnequalHuffman_NPC_Coding
-- name    : UnequalHuffman_NPC_Coding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:43:41.074064+00:00
-- url     : https://prove2.me/theorems/a5bb508c-ff69-40c7-8a97-462e5a9a306d
-- title:
--   Binary prefix codes: coding cost, weighted length, weighted number of ones, full codes, suppression, optima
-- statement:
--   A **binary prefix code** for $N$ source symbols is a tuple $C = (C_1,\dots,C_N)$ of finite words over $\{0,1\}$, no $C_i$ a prefix of another $C_j$ ($i \ne j$; this forces distinct codewords). In Lean a code is `C : Fin N → List Bool` with `false` for the letter $0$ and `true` for the letter $1$, and the prefix condition is the published `FuchsThesis.Coding.IsInstantaneous`.
--
--   For frequencies $w = (w_1,\dots,w_N)$ (a list of naturals) and letter costs $c_0, c_1$, with $|C_i|_0$, $|C_i|_1$ the numbers of zeros and ones:
--   $$\mathrm{cost}_{c_0,c_1}(C) = \sum_i w_i\,(c_0 |C_i|_0 + c_1 |C_i|_1),\qquad L(C) = \sum_i w_i |C_i|,\qquad R(C) = \sum_i w_i |C_i|_1 .$$
--
--   The **code tree** of $C$ has as vertices all prefixes of codewords (`IsCodeVertex`); left edges carry $0$, right edges $1$. The code is **full** (`IsFullCode`) if every vertex has none or both of its children $v0$, $v1$. A vertex $v$ is a **one-child vertex** with child $va$ (`IsOneChildVertex C v a`) if $va$ is a vertex and $v\bar a$ is not. **Suppressing** it (`suppress C v a`) deletes the letter $a$ at position $|v|$ from every codeword that begins with $va$ and leaves the other codewords unchanged.
--
--   A prefix code is **cost-optimal** (`IsCostOptimal c0 c1 w C`) if no prefix code has smaller cost, **length-optimal** (`IsLengthOptimal w C`) if no prefix code has smaller weighted length, and `IsOptCodeValue c0 c1 w v` says $v = \mathrm{OPT}_{\mathrm{code}}$: some prefix code costs $v$ and none costs less.
-- source:
--   Chandran and Gajjala, Binary Huffman Coding with Unequal Letter Costs Is NP-Complete, arXiv:2611.04444v1, p. 4 (prefix codes, cost), p. 5 (R(C)), p. 7 (§2.1 code trees, full trees, suppression)

import Mathlib
import Definitions.Def_FuchsThesis_Coding_IsInstantaneous

set_option autoImplicit false

namespace UnequalHuffman.NPC

open FuchsThesis.Coding

/-- `|s|₀`: the number of zeros of a binary word (the letter `0` is `false`). -/
def zeros (s : List Bool) : ℕ := s.count false

/-- `|s|₁`: the number of ones of a binary word (the letter `1` is `true`). -/
def ones (s : List Bool) : ℕ := s.count true

/-- The coding cost `cost_{c₀,c₁}(C) = ∑ᵢ wᵢ (c₀ |Cᵢ|₀ + c₁ |Cᵢ|₁)` of a code `C` for the
frequencies `w = (w₁, …, w_N)`: letter `0` costs `c₀`, letter `1` costs `c₁`. -/
def cost (c0 c1 : ℕ) (w : List ℕ) (C : Fin w.length → List Bool) : ℕ :=
  ∑ i, w.get i * (c0 * zeros (C i) + c1 * ones (C i))

/-- The ordinary weighted length `L(C) = ∑ᵢ wᵢ |Cᵢ|`. -/
def weightedLength (w : List ℕ) (C : Fin w.length → List Bool) : ℕ :=
  ∑ i, w.get i * (C i).length

/-- The weighted number of ones `R(C) = ∑ᵢ wᵢ |Cᵢ|₁`. -/
def weightedOnes (w : List ℕ) (C : Fin w.length → List Bool) : ℕ :=
  ∑ i, w.get i * ones (C i)

/-- `v` is a vertex of the code tree of `C`: a prefix of some codeword (the root is `[]`). -/
def IsCodeVertex {m : ℕ} (C : Fin m → List Bool) (v : List Bool) : Prop :=
  ∃ i, v <+: C i

/-- The code tree of `C` is full: every vertex has either no child or both children. -/
def IsFullCode {m : ℕ} (C : Fin m → List Bool) : Prop :=
  ∀ v, IsCodeVertex C v → (IsCodeVertex C (v ++ [false]) ↔ IsCodeVertex C (v ++ [true]))

/-- `v` is a vertex of the code tree of `C` whose only child is `v ++ [a]`. -/
def IsOneChildVertex {m : ℕ} (C : Fin m → List Bool) (v : List Bool) (a : Bool) : Prop :=
  IsCodeVertex C (v ++ [a]) ∧ ¬ IsCodeVertex C (v ++ [!a])

/-- Suppressing the one-child vertex `v` (whose child is `v ++ [a]`): every codeword passing
through the edge from `v` to `v ++ [a]` loses that letter; the other codewords are unchanged. -/
def suppress {m : ℕ} (C : Fin m → List Bool) (v : List Bool) (a : Bool) : Fin m → List Bool :=
  fun i => if v ++ [a] <+: C i then v ++ (C i).drop (v.length + 1) else C i

/-- `C` is an optimal (minimum-cost) binary prefix code for frequencies `w` and letter costs
`(c₀, c₁)`: it is a prefix code and no prefix code is cheaper. -/
def IsCostOptimal (c0 c1 : ℕ) (w : List ℕ) (C : Fin w.length → List Bool) : Prop :=
  IsInstantaneous C ∧ ∀ C' : Fin w.length → List Bool, IsInstantaneous C' →
    cost c0 c1 w C ≤ cost c0 c1 w C'

/-- `C` is a prefix code of minimum ordinary weighted length for the frequencies `w`. -/
def IsLengthOptimal (w : List ℕ) (C : Fin w.length → List Bool) : Prop :=
  IsInstantaneous C ∧ ∀ C' : Fin w.length → List Bool, IsInstantaneous C' →
    weightedLength w C ≤ weightedLength w C'

/-- `v` is the optimum value `OPT_code` of the coding instance `(w; c₀, c₁)`: some prefix code
has cost `v` and every prefix code costs at least `v`. -/
def IsOptCodeValue (c0 c1 : ℕ) (w : List ℕ) (v : ℤ) : Prop :=
  (∃ C : Fin w.length → List Bool, IsInstantaneous C ∧ (cost c0 c1 w C : ℤ) = v) ∧
  ∀ C : Fin w.length → List Bool, IsInstantaneous C → v ≤ (cost c0 c1 w C : ℤ)

end UnequalHuffman.NPC


