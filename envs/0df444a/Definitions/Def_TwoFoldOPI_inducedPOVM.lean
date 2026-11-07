-- Prove2me | Definitions.Def_TwoFoldOPI_inducedPOVM
-- name    : TwoFoldOPI_inducedPOVM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T22:43:26.422187+00:00
-- url     : https://prove2.me/theorems/ad8719f4-6af2-4523-8608-43ec2592a3fc
-- title:
--   The unordered-pair POVM of an isometry
-- statement:
--   For a linear map $V$ from one qudit into the space of ordered pairs $|a,a'\rangle$, measuring $V|\varphi\rangle$ in the standard basis and forgetting the order gives outcome $s$ with POVM element
--   $$E_s=\sum_{(a,a'):\ \{a,a'\}=s}V^\dagger|a,a'\rangle\langle a,a'|V .$$
--   The proof of Lemma 7.2 realizes its measurement this way.
-- source:
--   Ragavan, Shutty, Quantum Algorithms for OPI Variants Beyond Locality and Classical Decodability, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), §7.1, proof of Lemma 7.2, p. 39

import Mathlib

open scoped Matrix

namespace TwoFoldOPI

/-- **The unordered-pair POVM of an isometry into ordered pairs.**
Ragavan, Shutty, *Quantum Algorithms for OPI Variants Beyond Locality and Classical
Decodability*, arXiv:2610.00502 (version held, sha256 ef050ec0…62605), proof of Lemma 7.2, p.39: "Measuring |ψ_c⟩ in the standard basis gives (c, c′) or (c′, c)
… we output the unordered pair."

For `V : K^1 → K × K` (a matrix), measuring `V|φ⟩` in the basis `|a, a′⟩` and forgetting the
order gives outcome `s` with POVM element `E_s = Σ_{(a,a′) : {a,a′} = s} V† |a,a′⟩⟨a,a′| V`. -/
def inducedPOVM {K : Type*} [Fintype K] [DecidableEq K]
    (V : Matrix (K × K) (Fin 1 → K) ℂ) (u : Sym2 K) : Matrix (Fin 1 → K) (Fin 1 → K) ℂ :=
  ∑ ab ∈ Finset.univ.filter (fun ab : K × K => s(ab.1, ab.2) = u),
    Vᴴ * Matrix.single ab ab (1 : ℂ) * V

end TwoFoldOPI


