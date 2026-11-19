-- Prove2me | Definitions.Def_PPSLattice_Supplement_Construction53
-- name    : PPSLattice_Supplement_Construction53
-- status  : Definition
-- author  : @iris
-- created : 2026-11-18T07:51:57.705816+00:00
-- url     : https://prove2.me/theorems/355e7567-b3ca-4240-8b70-a9cf18458055
-- title:
--   Construction 5.3 — adaptive FBE compiler
-- statement:
--   Construction 5.3 combines two semi-static FBE key pairs, a selector bit, a $\lambda$-bit PPS tag, and a PPS public-key ciphertext. Encryption decodes selectors for the recipient-tag set and emits one PPS set key together with two FBE ciphertexts.
--
--   The accompanying accounting predicate records the exact component layout behind the four size formulas on page 34.
-- source:
--   Goyal–Yadugiri, STOC 2027 submission (manuscript sha256 7f9c493f…), Construction 5.3 and parameter display, pp.33–34

import Mathlib
import Definitions.Def_AvgPHETH_uniformDist
import Definitions.Def_BeyondDS_tup
import Definitions.Def_PPSLattice_Supplement_FBE
import Definitions.Def_PPSLattice_Supplement_PPSBit

open QAlgorithms.Complexity
set_option autoImplicit false

namespace PPSLattice.Supplement

private def tagIndex (tag : Str) : ℕ := decBin tag + 1

private def fbePkFields (pk : Str) : List Str := BeyondDS.untup pk

private def compilerTags (pks : List Str) : Finset ℕ :=
  (pks.map fun pk => tagIndex ((fbePkFields pk).getD 2 [])).toFinset

private def compilerSelectedPks (pks : List Str) (bits : List Bool) (flip : Bool) : List Str :=
  (pks.zip bits).map fun z =>
    let fs := fbePkFields z.1
    fs.getD (if xor z.2 flip then 1 else 0) []

/-- Construction 5.3, the two-key FBE compiler from a bit-message PPS (pp.33--34). Tags are
`λ`-bit strings interpreted as the one-based PPS indices `1 + value(tag)` in `[2^λ]`; this is a
bijection and is only an encoding convention. -/
noncomputable def construction53 (SSFBE : FBE) (E : PPS) : FBE where
  gsetup lam := (SSFBE.gsetup lam).bind fun fcrs => (E.gsetup lam (2 ^ lam)).map fun pcrs =>
    BeyondDS.tup [fcrs, pcrs]
  kgen lam crs :=
    let cs := BeyondDS.untup crs
    (SSFBE.kgen lam (cs.getD 0 [])).bind fun z0 =>
      (SSFBE.kgen lam (cs.getD 0 [])).bind fun z1 =>
        (PMF.uniformOfFintype Bool).bind fun s => (AvgPHETH.uniformDist lam).bind fun tag =>
          (E.pkEnc lam (2 ^ lam) (cs.getD 1 []) (tagIndex tag)).map fun ct =>
            (BeyondDS.tup [z0.1, z1.1, tag, ct], BeyondDS.tup [[s], if s then z1.2 else z0.2])
  enc lam crs pks mu :=
    let cs := BeyondDS.untup crs
    let S := compilerTags pks
    (E.mskgen lam (2 ^ lam) (cs.getD 1 [])).bind fun msk =>
      (E.kgen lam (2 ^ lam) (cs.getD 1 []) msk S).bind fun sk =>
        let bits := pks.map fun pk =>
          let fs := fbePkFields pk
          ((E.decode lam (2 ^ lam) (cs.getD 1 []) S sk (tagIndex (fs.getD 2 []))
            (fs.getD 3 [])).getD []).headD false
        (SSFBE.enc lam (cs.getD 0 []) (compilerSelectedPks pks bits false) mu).bind fun ct0 =>
          (SSFBE.enc lam (cs.getD 0 []) (compilerSelectedPks pks bits true) mu).map fun ct1 =>
            BeyondDS.tup [sk, ct0, ct1]
  dec lam crs pks i skCode ctCode :=
    let cs := BeyondDS.untup crs
    let sf := BeyondDS.untup skCode
    let cf := BeyondDS.untup ctCode
    let S := compilerTags pks
    let bits := pks.map fun pk =>
      let fs := fbePkFields pk
      ((E.decode lam (2 ^ lam) (cs.getD 1 []) S (cf.getD 0 []) (tagIndex (fs.getD 2 []))
        (fs.getD 3 [])).getD []).headD false
    let s := (sf.getD 0 []).headD false
    let ti := bits.getD (i - 1) false
    SSFBE.dec lam (cs.getD 0 []) (compilerSelectedPks pks bits (s ≠ ti)) i (sf.getD 1 [])
      (if s = ti then cf.getD 1 [] else cf.getD 2 [])

/-- Construction 5.3, exposed under the module's published definition name. -/
noncomputable def Construction53 (SSFBE : FBE) (E : PPS) : FBE := construction53 SSFBE E

/-- Exact component layout behind the p.34 size equations. Every output CRS has the two source
CRSs; every public key has two FBE public keys, a `λ`-bit tag and one PPS ciphertext; every secret
key has one selector bit and one FBE secret key; every ciphertext has one PPS set key and two FBE
ciphertexts. Hence, in the source's concatenation-size convention,
`|ct|=|pps.sk_S|+2|fbe.ct|`, `|crs|=|fbe.crs|+|pps.crs|`,
`|pk|=2|fbe.pk|+λ+|pps.ct|`, and `|sk|=1+|fbe.sk|`. -/
def Construction53ParameterAccounting (SSFBE : FBE) (E : PPS) : Prop :=
  let C := construction53 SSFBE E
  (∀ lam crs, crs ∈ (C.gsetup lam).support → (BeyondDS.untup crs).length = 2) ∧
  (∀ lam crs, crs ∈ (C.gsetup lam).support → ∀ z ∈ (C.kgen lam crs).support,
    (BeyondDS.untup z.1).length = 4 ∧ ((BeyondDS.untup z.1).getD 2 []).length = lam ∧
    (BeyondDS.untup z.2).length = 2 ∧ ((BeyondDS.untup z.2).getD 0 []).length = 1) ∧
  ∀ lam crs pks mu ct, ct ∈ (C.enc lam crs pks mu).support →
    (BeyondDS.untup ct).length = 3

end PPSLattice.Supplement


