-- Prove2me | Definitions.Def_PancakeHard_Literals
-- name    : PancakeHard_Literals
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:03.629949+00:00
-- url     : https://prove2.me/theorems/36620eb3-ac44-4011-b5c5-bd45f6ddeae3
-- title:
--   Definition 5 — the literals gadget $Literals(p,m)$ and the sequences $\Lambda^O_I$
-- statement:
--   For integers $p$ and $m$, $Literals(p,m)=(key_1,\dots,key_m,test_1,\dots,test_m,\Lambda)$ where $\Lambda=\langle L_1,\dots,L_m\rangle$ and, for every $i\in\llbracket 1;m\rrbracket$,
--   $$(key_i,test_i,L_i)=Lock(p+12(i-1)).$$
--   For disjoint subsets $O,I$ of $\llbracket 1;m\rrbracket$, $\Lambda^O_I$ is obtained from $\Lambda$ by replacing $L_i$ by the open lock $L_i^o$ for every $i\in O$, and by $\mathcal I^{p+12i-11}_{p+12i}$ for every $i\in I$. Thus $\Lambda^\emptyset_\emptyset=\Lambda$ and $\Lambda^\emptyset_{\llbracket 1;m\rrbracket}=\mathcal I^{p+1}_{p+12m}$.
--
--   Elements of $O$ are open locks and elements of $I$ are open locks that have moreover been tested; the gadget holds the locks of all literal occurrences of the formula.
--
--   **Formalization Note** `litKey p i` and `litTest p i` take the paper's index $i\ge 1$; `literals p m O I` is $\Lambda^O_I$, with $O$, $I$ finite sets of natural numbers (indices outside $\llbracket 1;m\rrbracket$ are ignored, and membership in $O$ is tested first, which is immaterial for disjoint $O$, $I$).
-- source:
--   Bulteau, Fertin, Rusu, Pancake Flipping Is Hard, arXiv:1111.0434v2, §3.2.1, p.9, Definition 5

import Mathlib
import Definitions.Def_PancakeHard_Lock

set_option autoImplicit false

namespace PancakeHard

/-- `keyᵢ` of `Literals(p, m)` (Definition 5, arXiv:1111.0434v2, §3.2.1, p.9):
`(keyᵢ, testᵢ, Lᵢ) = Lock(p + 12(i − 1))` for `i ∈ ⟦1 ; m⟧`, so `keyᵢ = p + 12(i − 1) + 10`.

**Formalization Note** Indices are the paper's, `i ∈ ⟦1 ; m⟧`; `i − 1` is truncated subtraction,
which never truncates for `i ≥ 1`. -/
def litKey (p i : ℕ) : ℕ := lockKey (p + 12 * (i - 1))

/-- `testᵢ` of `Literals(p, m)` (Definition 5, p.9): `testᵢ = p + 12(i − 1) + 7`. -/
def litTest (p i : ℕ) : ℕ := lockTest (p + 12 * (i - 1))

/-- The sequence `Λ^O_I` of `Literals(p, m)` (Definition 5, p.9): `Λ = ⟨L₁, L₂, …, L_m⟩` with
`Lᵢ` the closed lock of `Lock(p + 12(i − 1))`, in which, for disjoint `O, I ⊆ ⟦1 ; m⟧`,
* `Lᵢ` is replaced by `Lᵢᵒ` for all `i ∈ O`,
* `Lᵢ` is replaced by `𝓘^{p+12i−11}_{p+12i}` for all `i ∈ I`.

`Λ = Λ^∅_∅`.

**Formalization Note** Block `j = 0, …, m − 1` of the list is the paper's block `i = j + 1`, with
offset `p + 12j = p + 12(i − 1)`; `𝓘^{p+12i−11}_{p+12i}` is written `interval (p + 12j + 1)
(p + 12j + 12)`. Membership in `O` is tested first; for the disjoint `O`, `I` of the paper the order
does not matter. Indices of `O`, `I` outside `⟦1 ; m⟧` are ignored. -/
def literals (p m : ℕ) (O I : Finset ℕ) : List ℕ :=
  (List.range m).flatMap fun j =>
    if j + 1 ∈ O then lockOpen (p + 12 * j)
    else if j + 1 ∈ I then interval (p + 12 * j + 1) (p + 12 * j + 12)
    else lockSeq (p + 12 * j)

end PancakeHard


