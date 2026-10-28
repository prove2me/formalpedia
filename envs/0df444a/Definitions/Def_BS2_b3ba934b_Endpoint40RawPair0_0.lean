-- Prove2me | Definitions.Def_BS2_b3ba934b_Endpoint40RawPair0_0
-- name    : BS2_b3ba934b_Endpoint40RawPair0_0
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-26T16:21:56.457209+00:00
-- url     : https://prove2.me/theorems/fb857fbc-2dc1-4b30-9715-fe0bf395075e
-- title:
--   Sensitivity separation: Endpoint40RawPair0_0 (complete source module)
-- statement:
--   Complete Lean source module `Endpoint40RawPair0_0` from the two verified sensitivity separation proofs. The module supplies the definitions, auxiliary lemmas, and exact finite certificates used by its dependent modules. All original declarations and proof bodies are retained; only local import module paths are changed for Prove2Me. The final campaign goals are published separately as theorems with submitted solutions.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawPair0_0.lean; original SHA-256 95fb9724908cb8fcabfda66ae34c16117b209d4cb8e68ad2b25d702bc023a527; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40Prepared2

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace ThreeBoundNumeric.Endpoint40.RawPair0_0
open ThreeBoundFullProfile ClosureCertificate

def values : CostValues := {
  heads := #[#[1,181528495252010300000000000000000000000000000000000000000000000000001,181528495252010300000000000000000000000000000000000000000000000000001],#[1,180335570215853750000000000000000000000000000000000000000000000000001,180335570215853750000000000000000000000000000000000000000000000000001],#[1,1819509591345255500000000000000000000000000000000000000000000000001,1819509591345255500000000000000000000000000000000000000000000000001],#[0,181528495252010300000000000000000000000000000000000000000000000000000,199277885624578220000000000000000000000000000000000000000000000000000],#[0,180335570215853750000000000000000000000000000000000000000000000000000,199277885624578220000000000000000000000000000000000000000000000000000],#[0,1819509591345255500000000000000000000000000000000000000000000000000,3639019182690511000000000000000000000000000000000000000000000000000],#[0,180335570215853750000000000000000000000000000000000000000000000000000,180335570215853750000000000000000000000000000000000000000000000000000],#[0,1819509591345255500000000000000000000000000000000000000000000000000,1819509591345255500000000000000000000000000000000000000000000000000]]
  guard := 199277885624578220000000000000000000000000000000000000000000000000000
  negative := #[2678661091521830000000000000000000000000000000000000000000000000000,2678661091521830000000000000000000000000000000000000000000000000000,17852978040646582000000000000000000000000000000000000000000000000] }

def bound : ℕ := 77806142500417596074000000000000000000000000000000000000000000000000

theorem values_correct : coeffCheck 40 profile0 (recipe 0 0) (recipe 0 1) values=true := by
  decide +kernel

def check (k : ℕ) : Bool := indexedPreparedCheck fastRecords prepared2 (recipe 0 0)
  (recipe 0 1) values bound k

private theorem chunk0 : checkInterval check 0 32=true := by decide +kernel

private theorem chunk1 : checkInterval check 32 64=true := by decide +kernel

private theorem chunk2 : checkInterval check 64 96=true := by decide +kernel

private theorem chunk3 : checkInterval check 96 128=true := by decide +kernel

private theorem chunk4 : checkInterval check 128 160=true := by decide +kernel

private theorem chunk5 : checkInterval check 160 192=true := by decide +kernel

private theorem chunk6 : checkInterval check 192 224=true := by decide +kernel

private theorem chunk7 : checkInterval check 224 256=true := by decide +kernel

private theorem chunk8 : checkInterval check 256 288=true := by decide +kernel

private theorem chunk9 : checkInterval check 288 320=true := by decide +kernel

private theorem chunk10 : checkInterval check 320 352=true := by decide +kernel

private theorem chunk11 : checkInterval check 352 384=true := by decide +kernel

private theorem chunk12 : checkInterval check 384 416=true := by decide +kernel

private theorem chunk13 : checkInterval check 416 448=true := by decide +kernel

private theorem chunk14 : checkInterval check 448 480=true := by decide +kernel

private theorem chunk15 : checkInterval check 480 512=true := by decide +kernel

private theorem chunk16 : checkInterval check 512 544=true := by decide +kernel

private theorem chunk17 : checkInterval check 544 576=true := by decide +kernel

private theorem chunk18 : checkInterval check 576 608=true := by decide +kernel

private theorem chunk19 : checkInterval check 608 640=true := by decide +kernel

private theorem chunk20 : checkInterval check 640 672=true := by decide +kernel

private theorem chunk21 : checkInterval check 672 704=true := by decide +kernel

private theorem chunk22 : checkInterval check 704 736=true := by decide +kernel

private theorem chunk23 : checkInterval check 736 768=true := by decide +kernel

private theorem chunk24 : checkInterval check 768 800=true := by decide +kernel

private theorem chunk25 : checkInterval check 800 832=true := by decide +kernel

private theorem chunk26 : checkInterval check 832 864=true := by decide +kernel

private theorem chunk27 : checkInterval check 864 896=true := by decide +kernel

private theorem chunk28 : checkInterval check 896 928=true := by decide +kernel

private theorem chunk29 : checkInterval check 928 960=true := by decide +kernel

private theorem chunk30 : checkInterval check 960 992=true := by decide +kernel

private theorem chunk31 : checkInterval check 992 1024=true := by decide +kernel

private theorem chunk32 : checkInterval check 1024 1056=true := by decide +kernel

private theorem chunk33 : checkInterval check 1056 1088=true := by decide +kernel

private theorem chunk34 : checkInterval check 1088 1120=true := by decide +kernel

private theorem chunk35 : checkInterval check 1120 1152=true := by decide +kernel

private theorem chunk36 : checkInterval check 1152 1184=true := by decide +kernel

private theorem chunk37 : checkInterval check 1184 1216=true := by decide +kernel

private theorem chunk38 : checkInterval check 1216 1248=true := by decide +kernel

private theorem chunk39 : checkInterval check 1248 1280=true := by decide +kernel

private theorem chunk40 : checkInterval check 1280 1312=true := by decide +kernel

private theorem chunk41 : checkInterval check 1312 1344=true := by decide +kernel

private theorem chunk42 : checkInterval check 1344 1376=true := by decide +kernel

private theorem chunk43 : checkInterval check 1376 1408=true := by decide +kernel

private theorem chunk44 : checkInterval check 1408 1440=true := by decide +kernel

private theorem chunk45 : checkInterval check 1440 1472=true := by decide +kernel

private theorem chunk46 : checkInterval check 1472 1504=true := by decide +kernel

private theorem chunk47 : checkInterval check 1504 1536=true := by decide +kernel

private theorem chunk48 : checkInterval check 1536 1568=true := by decide +kernel

private theorem chunk49 : checkInterval check 1568 1600=true := by decide +kernel

private theorem chunk50 : checkInterval check 1600 1632=true := by decide +kernel

private theorem chunk51 : checkInterval check 1632 1664=true := by decide +kernel

private theorem chunk52 : checkInterval check 1664 1696=true := by decide +kernel

private theorem chunk53 : checkInterval check 1696 1728=true := by decide +kernel

private theorem chunk54 : checkInterval check 1728 1760=true := by decide +kernel

private theorem chunk55 : checkInterval check 1760 1792=true := by decide +kernel

private theorem chunk56 : checkInterval check 1792 1824=true := by decide +kernel

private theorem chunk57 : checkInterval check 1824 1856=true := by decide +kernel

private theorem chunk58 : checkInterval check 1856 1888=true := by decide +kernel

private theorem chunk59 : checkInterval check 1888 1920=true := by decide +kernel

private theorem chunk60 : checkInterval check 1920 1952=true := by decide +kernel

private theorem chunk61 : checkInterval check 1952 1984=true := by decide +kernel

private theorem chunk62 : checkInterval check 1984 2016=true := by decide +kernel

private theorem chunk63 : checkInterval check 2016 2048=true := by decide +kernel

private theorem chunk64 : checkInterval check 2048 2080=true := by decide +kernel

private theorem chunk65 : checkInterval check 2080 2112=true := by decide +kernel

private theorem chunk66 : checkInterval check 2112 2130=true := by decide +kernel

theorem checked : checkInterval check 0 2130=true :=
  (checkInterval_join check 0 1056 2130 (checkInterval_join check 0 512 1056 (checkInterval_join check 0 256 512 (checkInterval_join check 0 128 256 (checkInterval_join check 0 64 128 (checkInterval_join check 0 32 64 chunk0 chunk1) (checkInterval_join check 64 96 128 chunk2 chunk3)) (checkInterval_join check 128 192 256 (checkInterval_join check 128 160 192 chunk4 chunk5) (checkInterval_join check 192 224 256 chunk6 chunk7))) (checkInterval_join check 256 384 512 (checkInterval_join check 256 320 384 (checkInterval_join check 256 288 320 chunk8 chunk9) (checkInterval_join check 320 352 384 chunk10 chunk11)) (checkInterval_join check 384 448 512 (checkInterval_join check 384 416 448 chunk12 chunk13) (checkInterval_join check 448 480 512 chunk14 chunk15)))) (checkInterval_join check 512 768 1056 (checkInterval_join check 512 640 768 (checkInterval_join check 512 576 640 (checkInterval_join check 512 544 576 chunk16 chunk17) (checkInterval_join check 576 608 640 chunk18 chunk19)) (checkInterval_join check 640 704 768 (checkInterval_join check 640 672 704 chunk20 chunk21) (checkInterval_join check 704 736 768 chunk22 chunk23))) (checkInterval_join check 768 896 1056 (checkInterval_join check 768 832 896 (checkInterval_join check 768 800 832 chunk24 chunk25) (checkInterval_join check 832 864 896 chunk26 chunk27)) (checkInterval_join check 896 960 1056 (checkInterval_join check 896 928 960 chunk28 chunk29) (checkInterval_join check 960 992 1056 chunk30 (checkInterval_join check 992 1024 1056 chunk31 chunk32)))))) (checkInterval_join check 1056 1600 2130 (checkInterval_join check 1056 1312 1600 (checkInterval_join check 1056 1184 1312 (checkInterval_join check 1056 1120 1184 (checkInterval_join check 1056 1088 1120 chunk33 chunk34) (checkInterval_join check 1120 1152 1184 chunk35 chunk36)) (checkInterval_join check 1184 1248 1312 (checkInterval_join check 1184 1216 1248 chunk37 chunk38) (checkInterval_join check 1248 1280 1312 chunk39 chunk40))) (checkInterval_join check 1312 1440 1600 (checkInterval_join check 1312 1376 1440 (checkInterval_join check 1312 1344 1376 chunk41 chunk42) (checkInterval_join check 1376 1408 1440 chunk43 chunk44)) (checkInterval_join check 1440 1504 1600 (checkInterval_join check 1440 1472 1504 chunk45 chunk46) (checkInterval_join check 1504 1536 1600 chunk47 (checkInterval_join check 1536 1568 1600 chunk48 chunk49))))) (checkInterval_join check 1600 1856 2130 (checkInterval_join check 1600 1728 1856 (checkInterval_join check 1600 1664 1728 (checkInterval_join check 1600 1632 1664 chunk50 chunk51) (checkInterval_join check 1664 1696 1728 chunk52 chunk53)) (checkInterval_join check 1728 1792 1856 (checkInterval_join check 1728 1760 1792 chunk54 chunk55) (checkInterval_join check 1792 1824 1856 chunk56 chunk57))) (checkInterval_join check 1856 1984 2130 (checkInterval_join check 1856 1920 1984 (checkInterval_join check 1856 1888 1920 chunk58 chunk59) (checkInterval_join check 1920 1952 1984 chunk60 chunk61)) (checkInterval_join check 1984 2048 2130 (checkInterval_join check 1984 2016 2048 chunk62 chunk63) (checkInterval_join check 2048 2080 2130 chunk64 (checkInterval_join check 2080 2112 2130 chunk65 chunk66)))))))

theorem raw_bound : (rawAExpr 40 caps records (recipe 0 0) (recipe 0 1)).eval profile0≤bound := by
  apply rawA_le_of_prepared_checks 40 profile0 caps records fastRecords prepared2
    (recipe 0 0) (recipe 0 1) values bound fastRecords_valid fastRecords_rows
    (by decide) (by decide) values_correct
  · exact prepared2_correct
  · intro k hk
    have hlen := fastRecords_length
    exact checkInterval_sound check 0 2130 checked k (Nat.zero_le _) (by simpa [hlen] using hk)

end ThreeBoundNumeric.Endpoint40.RawPair0_0

#print axioms ThreeBoundNumeric.Endpoint40.RawPair0_0.raw_bound


