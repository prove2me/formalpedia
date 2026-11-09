-- Prove2me | Definitions.Def_AbelianCayleyHDX_encFVec
-- name    : AbelianCayleyHDX_encFVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T22:32:41.333946+00:00
-- url     : https://prove2.me/theorems/d01edbfa-a0c8-4c3f-95fe-dc64d0896907
-- title:
--   Binary encoding of a vector of $F^t$
-- statement:
--   For a finite field $F$ and a bijection $\mathrm{enc} : F \to \{0, \dots, |F| - 1\}$, a vector $a \in F^t$ is written as its length $t$ followed by each coordinate $\mathrm{enc}(a_i)$ in self-delimiting binary (the published `encNat`/`encList` encodings). The paper writes finite-field elements in binary.
-- source:
--   Songtao Mao, Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9 ("finite-field elements … are encoded in binary")

import Mathlib
import Definitions.Def_RSListDecodingCapacity_AllRates_Encoding

namespace AbelianCayleyHDX

open RSListDecodingCapacity.AllRates in
/-- **A vector of `F^t` in binary** (Mao, *Abelian Cayley High-Dimensional Expanders with Polylogarithmic Degree*, arXiv:2609.08937 (held version, sha256 6f5b0daa…75ba), Section 2.3, p.9: "finite-field elements … are
encoded in binary"): its length `t`, then each coordinate `a_i` as the number `enc(a_i)` in
self-delimiting binary, for a bijection `enc : F ≃ {0, …, |F| − 1}`. -/
def encFVec {F : Type*} [Fintype F] (enc : F ≃ Fin (Fintype.card F)) {t : ℕ} (a : Fin t → F) :
    List Bool :=
  encList (fun x => encNat (enc x).val) (List.ofFn a)

end AbelianCayleyHDX


