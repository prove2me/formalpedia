-- Prove2me | Definitions.Def_MonoidProdQ_Supplement_CallTree_run
-- name    : MonoidProdQ_Supplement_CallTree_run
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T11:07:22.177203+00:00
-- url     : https://prove2.me/theorems/20ed55b9-d187-4929-95ac-c4599a1a4826
-- title:
--   Execution of a call procedure: output, calls and unpredicted branches
-- statement:
--   Given functions $g_j$ ($j\in J$) and an input $x$, the **execution** of a call procedure $P$ on $x$ follows the unique root-to-leaf path in which each call to $g_j$ returns $g_j(x)$. It returns the triple
--
--   $$\bigl(\text{output at the leaf reached},\ \text{number of calls made},\ \text{number of unpredicted branches taken}\bigr).$$
--
--   Theorem 16 assumes that "every execution on $x\in D$ makes at most $q$ calls and takes an unpredicted branch at most $G$ times"; these are the second and third components.
--
--   **Formalization Note** A call whose taken branch is not the designated predicted one, including every call that designates no predicted branch, counts as one unpredicted branch.
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16, p.31

import Definitions.Def_MonoidProdQ_Supplement_CallTree

universe u v w x

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 16, p.31: the execution of a call
procedure (`CallTree`) on an input `x`, where the call to `g_j` returns `g j x`. It returns the
triple (output, number of calls made, number of times an unpredicted branch was taken) along the
execution path: "every execution on x ∈ D makes at most q calls and takes an unpredicted branch at
most G times".

**Formalization Note.** A call whose taken branch is not the designated predicted one (including
every call with no predicted branch) counts as one unpredicted branch. -/
def CallTree.run {J : Type u} {Γ : J → Type v} {O : Type w} {X : Type x}
    (g : ∀ j, X → Γ j) (x : X) : CallTree J Γ O → O × ℕ × ℕ
  | .leaf o => (o, 0, 0)
  | .node j _ branch predicted child =>
      let r := (child (branch (g j x))).run g x
      (r.1, r.2.1 + 1, r.2.2 + if predicted = some (branch (g j x)) then 0 else 1)

end MonoidProdQ.Supplement


