-- Prove2me | Definitions.Def_PRUPermLayer_plusProj
-- name    : PRUPermLayer_plusProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:25:55.633658+00:00
-- url     : https://prove2.me/theorems/9a4615c4-22b2-4cb9-a290-b0f1f6a8e3bd
-- title:
--   Projector $|+_N\rangle\langle +_N|$ onto the uniform superposition
-- statement:
--   The **uniform superposition** on $N$ labels is $|+_N\rangle = N^{-1/2} \sum_{x} |x\rangle$; for $N = 2^n$ it is the product state $|+\rangle^{\otimes n}$ with $|+\rangle = (|0\rangle + |1\rangle)/\sqrt 2$. Its projector $|+_N\rangle\langle +_N|$ has every matrix entry equal to $1/N$.
-- source:
--   Shen–Zhong, Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)

import Mathlib

namespace PRUPermLayer

/-- The projector `|+_N⟩⟨+_N|` onto the uniform superposition `|+_N⟩ = N^{−1/2} Σₓ |x⟩`
(Shen–Zhong, *Pseudorandom Unitaries from a Random Permutation and One Layer of Single-Qubit Gates*, manuscript (STOC 2027 submission; held version sha256 395fcfa3…5bcb), §2.1, p.8 (PDF p.10)). Every entry is `1/N`.

**Formalization Note** For `N = 2ⁿ` this is `|+⟩⟨+|^{⊗n}` with `|+⟩ = (|0⟩ + |1⟩)/√2`. -/
noncomputable def plusProj (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun _ _ => (N : ℂ)⁻¹

end PRUPermLayer


