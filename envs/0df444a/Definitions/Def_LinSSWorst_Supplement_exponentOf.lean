-- Prove2me | Definitions.Def_LinSSWorst_Supplement_exponentOf
-- name    : LinSSWorst_Supplement_exponentOf
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T12:44:26.875706+00:00
-- url     : https://prove2.me/theorems/7f53f23f-f4d5-4ed1-a1a6-f77ab999b2b8
-- title:
--   Share-size measures $\mathrm{SSize}$, $\mathrm{LSSize}$ and the secret-sharing exponents $S$, $S_\ell$ (complexity conventions [AN21])
-- statement:
--   For an $n$-party access structure $f$:
--   - $\mathrm{SSize}(f)$ is the minimum total share size of a secret-sharing scheme for one-bit secrets realizing $f$;
--   - $\mathrm{LSSize}(f)$ is the minimum total share length $\sum_i\ell_i$ of a linear scheme realizing $f$ (over $\mathbb F_2$, the field of one-bit secrets, so share length equals share size in bits);
--   - $\mathrm{QSize}(f)$ is the minimum total share size of a scheme with quadratic sharing and reconstruction over $\mathbb F_2$ realizing $f$.
--
--   For a size measure $\mathrm{Size}$, the exponent of the sequence of all access structures is
--   $$\limsup_{n\to\infty}\ \max_{f\ n\text{-party access structure}}\ \frac1n\log_2\mathrm{Size}(f).$$
--   With $\mathrm{SSize}$ this is the **secret-sharing exponent** $S$, with $\mathrm{LSSize}$ the **linear exponent** $S_\ell$, and with $\mathrm{QSize}$ the quadratic exponent.
--
--   These are the quantities compared by Theorems 1.5 and 1.6.
--
--   **Formalization Note** Sizes take values in $[0,\infty]$ (the minimum is an infimum over all schemes, in `Type`), and the logarithm, maximum and $\limsup$ are computed in the extended reals, so $\log_2 0=-\infty$ and no junk value arises. At $n=0$ the factor $1/n$ is $0$, which does not affect the $\limsup$.
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), App. A.1, Complexity conventions [AN21], p.30

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_Supplement_RealizesGen
import Definitions.Def_LinSSWorst_Supplement_RealizesQuad

open ENNReal

namespace LinSSWorst.Supplement

/-- The base-two logarithm `log₂ x` of an extended nonnegative real, as an extended real:
`log₂ 0 = −∞`, `log₂ ∞ = +∞`, and `log₂ x = Real.log x / Real.log 2` otherwise. From O. Nir,
*Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of
2026-11-02, sha256 5521cfdb…), §2.1 and App. A.1, p.30 (logarithms are base two). -/
noncomputable def log2E (x : ℝ≥0∞) : EReal :=
  ((1 / Real.log 2 : ℝ) : EReal) * ENNReal.log x

/-- The **secret-sharing exponent of the sequence of all access structures** for a size measure
(complexity conventions [AN21], App. A.1, p.30): given a size `size n f` of every `n`-party access
structure `f`, the exponent of `f` is `n⁻¹ · log₂ size(f)`, the exponent of the collection of all `n`-party
access structures is the maximum of these over `f`, and the exponent of the sequence is
`lim sup_{n → ∞}` of that maximum.

**Formalization Note.** Everything is computed in the complete lattice `EReal` (sizes in `ℝ≥0∞`), so the
supremum, the logarithm (`log₂ 0 = −∞`) and the `lim sup` are never junk values; the maximum over the
finitely many access structures is the supremum. At `n = 0` the factor `n⁻¹` is `0`, which does not affect
the `lim sup`. -/
noncomputable def exponentOf (size : (n : ℕ) → ((Fin n → Bool) → Bool) → ℝ≥0∞) : EReal :=
  Filter.limsup (fun n : ℕ =>
    ⨆ (f : (Fin n → Bool) → Bool) (_ : IsAccessStructure f),
      ((1 / (n : ℝ) : ℝ) : EReal) * log2E (size n f)) Filter.atTop

/-- `SSize(f)` (App. A.1, p.30): the minimum total share size `Σ_j log₂ |S_j|` of a secret-sharing scheme
for one-bit secrets that realizes `f` (Definition A.2).

**Formalization Note.** The minimum is the infimum in `ℝ≥0∞` over all schemes `Bool × R → Π_j σ j`
with `R` a nonempty finite type of random strings and finite share domains `σ j`, all in `Type`. -/
noncomputable def SSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ≥0∞ :=
  sInf {c | ∃ (R : Type) (_ : Fintype R) (_ : Nonempty R) (σ : Fin n → Type)
    (_ : ∀ i, Fintype (σ i)) (scheme : Bool → R → (i : Fin n) → σ i),
      RealizesGen f scheme ∧ c = ENNReal.ofReal (totalShareSize σ)}

/-- `LSSize(f)` (App. A.1, p.30): the minimum total share length `Σ_i ℓ_i` of a linear secret-sharing
scheme (Definition A.3) that realizes `f`, over `F₂`.

**Formalization Note.** Exponents are for one-bit secrets (App. A.1) and a linear scheme's secret lies in
its field, so linear schemes for one-bit secrets are linear schemes over `F₂ = ZMod 2`; their total share
length in elements of `F₂` is their total share size in bits. -/
noncomputable def LSSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ≥0∞ :=
  sInf {c | ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
    (scheme : (ZMod 2 × (Fin ℓr → ZMod 2)) →ₗ[ZMod 2] ((i : Fin n) → Fin (ℓ i) → ZMod 2)),
      Realizes f scheme ∧ c = ((∑ i, ℓ i : ℕ) : ℝ≥0∞)}

/-- The minimum total share size `Σ_i ℓ_i` (bits) of a secret-sharing scheme for one-bit secrets with
quadratic sharing and reconstruction over `F₂` (p.5, [BOP21]) that realizes `f`. -/
noncomputable def QSize (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ≥0∞ :=
  sInf {c | ∃ (ℓr : ℕ) (ℓ : Fin n → ℕ)
    (sh : (i : Fin n) → Fin (ℓ i) → MvPolynomial (Option (Fin ℓr)) (ZMod 2)),
      RealizesQuad f sh ∧ c = ((∑ i, ℓ i : ℕ) : ℝ≥0∞)}

/-- The **secret-sharing exponent** `S` of all access structures (App. A.1, p.30; p.5). -/
noncomputable def genExponent : EReal := exponentOf SSize

/-- The **linear secret-sharing exponent** `S_ℓ` of all access structures (App. A.1, p.30; p.5). -/
noncomputable def linExponent : EReal := exponentOf LSSize

/-- The **quadratic secret-sharing exponent** of all access structures (p.6). -/
noncomputable def quadExponent : EReal := exponentOf QSize

end LinSSWorst.Supplement


