-- Prove2me | Definitions.Def_QuantumPRC_PRF
-- name    : QuantumPRC_PRF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:36:35.714239+00:00
-- url     : https://prove2.me/theorems/baff90a7-b7b9-4f73-a139-e13aec669fa5
-- title:
--   Quantum oracle access (82), pseudorandom functions and permutations (Definitions 3.17, 3.18)
-- statement:
--   For $g:\{0,1\}^n\to\{0,1\}^m$, **quantum oracle access** to $g$ is the unitary
--
--   $$
--   |x\rangle|y\rangle\mapsto|x\rangle|y\oplus g(x)\rangle\qquad(82).
--   $$
--
--   1. A deterministic polynomial-time $F:\{0,1\}^\lambda\times\{0,1\}^{n(\lambda)}\to\{0,1\}^{m(\lambda)}$ is a **PRF** if every QPT adversary distinguishes oracle access to $f_k=F(k,\cdot)$, $k\leftarrow\{0,1\}^\lambda$, from oracle access to a uniformly random function $\{0,1\}^{n(\lambda)}\to\{0,1\}^{m(\lambda)}$ with advantage $\mathsf{negl}(\lambda)$.
--   2. Deterministic polynomial-time $\Pi,\Pi^{-1}$ form a **PRP** if $\pi_k=\Pi(k,\cdot)$ and $\pi_k^{-1}=\Pi^{-1}(k,\cdot)$ are mutually inverse permutations of $\{0,1\}^{n(\lambda)}$ and every QPT adversary with oracle access to both $\pi_k$ and $\pi_k^{-1}$ distinguishes them from a uniformly random permutation $\pi$ (with $\pi$ and $\pi^{-1}$) with advantage $\mathsf{negl}(\lambda)$.
--
--   These are the post-quantum PRFs and PRPs used in Construction 6.5 and Construction 7.2.
--
--   **Formalization Note** Both oracles of a PRP are given in the form (82). "Let $n,m$ be polynomials" is a hypothesis of the statements that use these predicates.
-- source:
--   Hsieh, Yamada, Quantum Pseudorandom Error-Correcting Codes, arXiv:2609.38986 (version of October 29, 2026, sha256 6901b59d1cbcf0183f98f2951ab17c9baae4e341e5b2a3c767d1ae93e77976db), Definition 3.17, p.21; Definition 3.18, p.21; Definition 6.1, Eq. (82), p.33

import Mathlib
import Definitions.Def_QuantumPRC_Assumption5

open Matrix

namespace QuantumPRC

/-- The first `n` bits of a string of length `n + m`. -/
def leftPart {n m : ℕ} (z : Bits (n + m)) : Bits n := fun i => z (Fin.castAdd m i)

/-- The last `m` bits of a string of length `n + m`. -/
def rightPart {n m : ℕ} (z : Bits (n + m)) : Bits m := fun j => z (Fin.natAdd n j)

/-- The unitary `|x⟩|y⟩ ↦ |x⟩|y ⊕ g(x)⟩` of a function `g : {0,1}^n → {0,1}^m`, Eq. (82). -/
def xorUnitary {n m : ℕ} (g : Bits n → Bits m) : Matrix (Bits (n + m)) (Bits (n + m)) ℂ :=
  fun z' z => if z' = Fin.append (leftPart z) (xorB (rightPart z) (g (leftPart z))) then 1 else 0

/-- **Quantum oracle access to a function**: the channel of the unitary `xorUnitary g`
(arXiv:2609.38986, Definition 6.1, Eq. (82), p.33: "`A^g` can query the unitary that maps
`|x⟩|y⟩ ↦ |x⟩|y ⊕ g(x)⟩`"). This is the query model of Definitions 3.17, 3.18 and 6.1. -/
def xorOracle {n m : ℕ} (g : Bits n → Bits m) : Superop (Bits (n + m)) (Bits (n + m)) :=
  conjMap (xorUnitary g)

/-- **PRF candidate**, Definition 3.17 syntax: a keyed function `F : {0,1}^λ × {0,1}^{n(λ)} →
{0,1}^{m(λ)}`. -/
structure PRF (n m : ℕ → ℕ) where
  F : ∀ lam, Bits lam → Bits (n lam) → Bits (m lam)

/-- **Pseudorandom function**, Definition 3.17. Hsieh, Yamada, arXiv:2609.38986 (sha256 6901b59d…),
p.21: "A deterministic polynomial-time algorithm `F : {0,1}^λ × {0,1}^{n(λ)} → {0,1}^{m(λ)}` is a
pseudorandom function (PRF) if, for any QPT adversary `A`,
`|Pr_{k←{0,1}^λ}[1 ← A^{f_k}(1^λ)] − Pr_f[1 ← A^f(1^λ)]| ≤ negl(λ)`, where `f_k(·) := F(k, ·)`. Here, `f`
is a uniformly random function `{0,1}^{n(λ)} → {0,1}^{m(λ)}`."

**Formalization Note.** Queries are quantum, in the form (82); "Let `n, m` be polynomials" is a
hypothesis of the statements that use this predicate. -/
def PRF.IsPRF {n m : ℕ → ℕ} (P : PRF n m) : Prop :=
  IsPolyFamily (α := fun lam => Bits lam × Bits (n lam)) (fun lam a => P.F lam a.1 a.2)
    (fun _ a => [bits a.1, bits a.2]) (fun _ y => bits y) ∧
  ∀ A : ∀ lam, OCirc (n lam + m lam) (n lam + m lam) 1, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun k : Bits lam => (A lam).accept (fun _ => xorOracle (P.F lam k)) []) -
        avg (fun f : Bits (n lam) → Bits (m lam) => (A lam).accept (fun _ => xorOracle f) [])|
        ≤ ν lam

/-- **PRP candidate**, Definition 3.18 syntax: keyed maps `Π, Π⁻¹ : {0,1}^λ × {0,1}^{n(λ)} →
{0,1}^{n(λ)}`. -/
structure PRP (n : ℕ → ℕ) where
  P : ∀ lam, Bits lam → Bits (n lam) → Bits (n lam)
  Pinv : ∀ lam, Bits lam → Bits (n lam) → Bits (n lam)

/-- **Pseudorandom permutation**, Definition 3.18. Hsieh, Yamada, arXiv:2609.38986 (sha256
6901b59d…), p.21: "A pair of deterministic polynomial-time algorithms `Π` and `Π⁻¹` is a
pseudorandom permutation (PRP) if `π_k(·) := Π(k, ·)` and `π_k⁻¹(·) := Π⁻¹(k, ·)` are permutations over
`{0,1}^{n(λ)}` such that `π_k ∘ π_k⁻¹` and `π_k⁻¹ ∘ π_k` are the identity, and, for any QPT adversary `A`,
`|Pr_{k←{0,1}^λ}[1 ← A^{π_k, π_k⁻¹}(1^λ)] − Pr_π[1 ← A^{π, π⁻¹}(1^λ)]| ≤ negl(λ)`. Here, `π` is a
uniformly random permutation."

**Formalization Note.** The adversary has two oracles, `π` and `π⁻¹`, each in the form (82). -/
def PRP.IsPRP {n : ℕ → ℕ} (P : PRP n) : Prop :=
  IsPolyFamily (α := fun lam => Bits lam × Bits (n lam)) (fun lam a => P.P lam a.1 a.2)
    (fun _ a => [bits a.1, bits a.2]) (fun _ y => bits y) ∧
  IsPolyFamily (α := fun lam => Bits lam × Bits (n lam)) (fun lam a => P.Pinv lam a.1 a.2)
    (fun _ a => [bits a.1, bits a.2]) (fun _ y => bits y) ∧
  (∀ lam k, Function.LeftInverse (P.Pinv lam k) (P.P lam k) ∧
    Function.RightInverse (P.Pinv lam k) (P.P lam k)) ∧
  ∀ A : ∀ lam, OCirc (n lam + n lam) (n lam + n lam) 2, IsUniformAdv A →
    ∃ ν : ℕ → ℝ, Negligible ν ∧ ∀ lam,
      |avg (fun k : Bits lam =>
          (A lam).accept ![xorOracle (P.P lam k), xorOracle (P.Pinv lam k)] []) -
        avg (fun π : Equiv.Perm (Bits (n lam)) =>
          (A lam).accept ![xorOracle π, xorOracle π.symm] [])| ≤ ν lam

end QuantumPRC


