-- Prove2me | Definitions.Def_MantriCVQ_nodeVal
-- name    : MantriCVQ_nodeVal
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T11:08:40.193732+00:00
-- url     : https://prove2.me/theorems/0c01c0f7-8399-4939-b93a-c2bc70b01806
-- title:
--   Values and validity of nodes
-- statement:
--   In a leaf table $Y$, a leaf has the bit stored at it. A node of dimension $m$ has the value $R_s$, for a secret $s$ whose codeword is the node's code table, where $R$ is its data table. A tree is **valid** if every child is valid and the code table is the codeword of some secret.
--
--   **Formalization Note** The value is $\exists s,\ (L=C_m(s,\cdot))\wedge R_s=1$. On a valid tree of a code family the secret is unique, so this is the paper's value.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §4.1, p. 16 (PDF p. 18)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ

open Classical in
/-- The value of the node with address `w` in a leaf table `Y`, indexed by flat leaf addresses, where
the node's subtree has the listed dimensions from its root down (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §4.1, p. 16 (PDF p. 18)). A leaf has the bit stored at it. At a node of dimension `m`
the value is `R_s` for a secret `s` whose codeword is the code table: "the value of the node is `R_s`".

**Formalization Note** On a valid tree of a code family the secret is unique, so the existential
formula below is the paper's value. -/
noncomputable def nodeVal (C : (m : ℕ) → Bits m → Bits m → Bool) :
    List ℕ → (Str → Bool) → Str → Bool
  | [], Y, w => Y w
  | m :: ms, Y, w =>
    decide (∃ s : Bits m,
      (∀ x : Bits m, nodeVal C ms Y (w ++ false :: List.ofFn x) = C m s x) ∧
        nodeVal C ms Y (w ++ true :: List.ofFn s) = true)

/-- Validity of the subtree at `w` (§4.1, p. 16: "Every tree of height zero is valid, and a tree of
height `j ≥ 1` is valid if every child is valid and the table of code-child values … is the codeword
of some secret `s`"). -/
def Valid (C : (m : ℕ) → Bits m → Bits m → Bool) : List ℕ → (Str → Bool) → Str → Prop
  | [], _, _ => True
  | m :: ms, Y, w =>
    (∀ (b : Bool) (x : Bits m), Valid C ms Y (w ++ b :: List.ofFn x)) ∧
      ∃ s : Bits m, ∀ x : Bits m, nodeVal C ms Y (w ++ false :: List.ofFn x) = C m s x

end MantriCVQ


