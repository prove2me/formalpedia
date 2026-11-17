-- Prove2me | Definitions.Def_MantriCVQ_Supplement_nodeValNoisy
-- name    : MantriCVQ_Supplement_nodeValNoisy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:03:29.394364+00:00
-- url     : https://prove2.me/theorems/4f97d746-ffc3-4a7f-a83a-1c0ed1009c28
-- title:
--   Value and validity of a tree with noise rate $\eta$ (§7.4)
-- statement:
--   Fix a code family $C$ and a noise rate $\eta$. For a leaf table $Y$ and a node at address $w$ whose subtree has the listed dimensions:
--
--   1. the **value** of a leaf is its bit; the value of a node of dimension $m$ is the value of its data child at the secret $s$, where $s$ is a string whose codeword $C_m(s,\cdot)$ is within relative distance $\eta$ of the code table $x\mapsto\mathrm{val}(w0x)$, that is, $G^C_{m,\eta}(L,R)=R_s$;
--   2. every tree of height zero is **valid with noise rate $\eta$**, and a tree of height $j\ge1$ is valid with noise rate $\eta$ if every child is valid with noise rate $\eta$ and its code table is within relative distance $\eta$ of some codeword.
--
--   For $0\le\eta<1/4$ the secret of a valid node is unique, because distinct codewords have relative distance $1/2>2\eta$. For $\eta=0$ these are the exact value and validity of Section 4, and every exact instance is valid with every noise rate, with the same value.
--
--   These notions describe the instances of Theorem 7.4 and Appendix A.
--
--   The relative Hamming distance $\mathrm{dist}(L,c)=|\{x\in\mathbb F_2^m:L(x)\neq c(x)\}|/2^m$ is the published `AvoidPlast.relDist`.
--
--   **Formalization Note** "Within" is $\le\eta$, so exact codewords are included. The value is written with an existential over secrets, as in the published exact value.
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), §7.4, p. 41 (PDF p. 43); §3.2, p. 15 (PDF p. 17)

import Mathlib
import Definitions.Def_AvoidPlast_relDist
import Definitions.Def_QAlgorithms_Defs_Complexity

open QAlgorithms.Complexity

namespace MantriCVQ.Supplement

open Classical in
/-- The value of the node with address `w` in a leaf table `Y` for noise rate `η`, where the node's
subtree has the listed dimensions from its root down (Mantri, arXiv:2610.37635 (PDF sha256
d1fab777…1d0b33), §7.4, p. 41 (PDF p. 43): "The secret of such a node is the unique string whose
codeword is within relative distance `η` of the code table … and the value of the node is the value of
the data child at the secret"; §3.2, p. 15 (PDF p. 17), `G^C_{m,η}(L, R) = R_s`). A leaf has the bit
stored at it.

**Formalization Note** "Within" is `≤ η`. For `0 ≤ η < 1/4` the secret is unique (distinct codewords
of a code family have relative distance `1/2 > 2η`), so the existential formula below is the paper's
value. For `η = 0` this is the published exact `MantriCVQ.nodeVal`. The relative Hamming distance is the
published `AvoidPlast.relDist` (the fraction of positions of `F₂^m` where the tables differ). -/
noncomputable def nodeValNoisy (C : (m : ℕ) → Bits m → Bits m → Bool) (η : ℝ) :
    List ℕ → (Str → Bool) → Str → Bool
  | [], Y, w => Y w
  | m :: ms, Y, w =>
    decide (∃ s : Bits m,
      AvoidPlast.relDist (fun x : Bits m => nodeValNoisy C η ms Y (w ++ false :: List.ofFn x)) (C m s) ≤ η ∧
        nodeValNoisy C η ms Y (w ++ true :: List.ofFn s) = true)

/-- Validity with noise rate `η` of the subtree at `w` (§7.4, p. 41 (PDF p. 43): "every tree of height
zero is valid with noise rate `η`, and a tree of height `j ≥ 1` is valid with noise rate `η` if every
child is valid with noise rate `η` and the table of code-child values is within relative distance `η`
of a codeword").

**Formalization Note** "Within" is `≤ η`; for `η = 0` this is the published exact `MantriCVQ.Valid`. -/
def ValidNoisy (C : (m : ℕ) → Bits m → Bits m → Bool) (η : ℝ) :
    List ℕ → (Str → Bool) → Str → Prop
  | [], _, _ => True
  | m :: ms, Y, w =>
    (∀ (b : Bool) (x : Bits m), ValidNoisy C η ms Y (w ++ b :: List.ofFn x)) ∧
      ∃ s : Bits m,
        AvoidPlast.relDist (fun x : Bits m => nodeValNoisy C η ms Y (w ++ false :: List.ofFn x)) (C m s) ≤ η

end MantriCVQ.Supplement


