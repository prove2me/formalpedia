-- Prove2me | Definitions.Def_CompNonlocal_Certificate_senderObs
-- name    : CompNonlocal_Certificate_senderObs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:45:45.936988+00:00
-- url     : https://prove2.me/theorems/91d407c9-9c78-40f5-b322-0de75d7a3911
-- title:
--   The sender observables $M_j$
-- statement:
--   For fixed $(x,a)$, the acceptance effect $F_{x,a}$ on Bob's qubit and $S$ is expanded as
--   $$2F_{x,a}-I=I\otimes M_0+\sum_{j=1}^3\sigma_j\otimes M_j$$
--   (Bob's qubit first). On the block of $S$ with questions $(x,y)$, $M_j=\sum_b\operatorname{Tr}(\sigma_jB^y_b)\,V_{a,b,x,y}$, where $V$ is the verifier's accept effect on td.
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), §8.3, Eq. (28), p.37

import Mathlib
import Definitions.Def_CompNonlocal_Certificate
import Definitions.Def_CompNonlocal_ICirc_qubitEffect
import Definitions.Def_CompNonlocal_pauli

set_option autoImplicit false

namespace CompNonlocal

open QAlgorithms.Complexity

/-- The sender observables `M_j` (`j = 1, 2, 3`) of the §8.3 decoder analysis, for one question
outcome. Głuch, Morimae, *From Computational Nonlocality to Public-Key Encryption and Commitments*,
manuscript (STOC 2027 submission, sha256 e245edd7…), Eq. (28), p.37: "Recall that F_{x,a} is the
acceptance effect acting jointly on Bob's input qubit and the sender's register S, for fixed
transcript (x, a). We expand its centered version in the Pauli basis of Bob's qubit:
2F_{x,a} − I = I ⊗ M_0 + Σ_{j=1}^3 σ_j ⊗ M_j", with "the coefficients M_0, …, M_3 act[ing] on S".

**Formalization Note** On the block of `S` with question outcome `o = x ++ y`,
`F_{x,a} = Σ_b B^y_b ⊗ V_{a,b,o}` (Bob's effect, then the verifier's accept effect on `td`), so
`M_j = ½ Tr_B((σ_j ⊗ I)(2F − I)) = Σ_b Tr(σ_j B^y_b) · V_{a,b,o}`; this returns that operator on the
verifier's register. `j ∈ Fin 3` is the paper's `j ∈ {1, 2, 3}`. -/
noncomputable def Certificate.senderObs (c : Certificate) (κ : ℕ) (o a : Str) (j : Fin 3) :
    Matrix (Bits (c.Qg κ).outQ.length) (Bits (c.Qg κ).outQ.length) ℂ :=
  ∑ b : Bits (c.B κ).outC.length,
    (pauli j * (c.B κ).qubitEffect (o.drop (c.lx κ)) (fun t => decide (t = List.ofFn b))).trace •
      c.valEffect κ a (List.ofFn b) o

end CompNonlocal


