-- Prove2me | Definitions.Def_TwoFoldOPI_Supplement_fnOracle
-- name    : TwoFoldOPI_Supplement_fnOracle
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T13:52:42.508818+00:00
-- url     : https://prove2.me/theorems/c00a3060-246a-4b8e-886b-f632ed8e9c64
-- title:
--   The reversible oracle $|x,z\rangle\mapsto|x,z\oplus f(x)\rangle$
-- statement:
--   For a function $f:\{0,1\}^{a}\to\{0,1\}^{b}$, its **reversible oracle** acts on $a+b$ qubits as the permutation
--   $$|x,z\rangle\mapsto|x,z\oplus f(x)\rangle .$$
--
--   This is the paper's convention for classical function oracles, used for the oracles $H_i$ of Section 11, for represented instances (Theorem 5.28) and for the random oracle of Theorem 11.10.
--
--   **Formalization Note** The matrix is given an arity argument; if the arity is not $a+b$ it is the identity, which gives a program declaring a different arity no information.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, Computational conventions, p. 26

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic

namespace TwoFoldOPI

namespace Supplement

open QAlgorithms

/-- **The reversible oracle `|x, z⟩ ↦ |x, z ⊕ f(x)⟩` of a function on bit strings.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §5.2, "Computational conventions", p.26: "Classical function oracles use reversible
evaluation, |x, z⟩ ↦ |x, z ⊕ H(x)⟩, with a fixed binary encoding of the output."

For `f : {0,1}^{inW} → {0,1}^{outW}`, `fnOracle a inW outW f` acts on `a` qubits. If
`a = inW + outW`, the first `inW` wires hold `x` and the last `outW` wires hold `z`, and it is the
permutation matrix of `(x, z) ↦ (x, z ⊕ f(x))`. Otherwise it is the identity.

**Formalization Note.** The arity guard lets the oracle be handed to a program whose declared
oracle arity is a field of the program: a program declaring a different arity gets the identity,
which gives it no information. -/
noncomputable def fnOracle (a inW outW : ℕ) (f : (Fin inW → Bool) → (Fin outW → Bool)) :
    Matrix (Qubits a) (Qubits a) ℂ :=
  if h : a = inW + outW then
    Matrix.of fun y z =>
      if (∀ i : Fin inW, y (Fin.cast h.symm (Fin.castAdd outW i)) =
            z (Fin.cast h.symm (Fin.castAdd outW i))) ∧
          ∀ j : Fin outW, y (Fin.cast h.symm (Fin.natAdd inW j)) =
            xor (z (Fin.cast h.symm (Fin.natAdd inW j)))
              (f (fun i => z (Fin.cast h.symm (Fin.castAdd outW i))) j)
      then 1 else 0
  else 1

end Supplement

end TwoFoldOPI


