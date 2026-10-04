-- Prove2me | Definitions.Def_Yukon_2c3d69aa75eca8413e194720
-- name    : Yukon_2c3d69aa75eca8413e194720
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T16:46:30.936556+00:00
-- url     : https://prove2.me/theorems/66816a00-3c34-4b62-948c-bdbfdf495ab2
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S0.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.MovingFiberPackingSound6814S0.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/MovingFiberPackingSound6814S0.lean
--
--   yukon-proof-operation:certificate-split-0ebe5d2479124c4f904d783056e7e20a351b7b9c2a23c1ac8e91f0b28df0dc79
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYTA1NzQwY2Q0ZTE1NjFkNTZhMzBlODhlOTE4MThjNWMzYWMyNGZjMDIwZmQzNmQwMjU2YzVlNjU0NDlkZmZkYSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTBlYmU1ZDI0NzkxMjRjNGY5MDRkNzgzMDU2ZTdlMjBhMzUxYjdiOWMyYTIzYzFhYzhlOTFmMGIyOGRmMGRjNzkiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl8yYzNkNjlhYTc1ZWNhODQxM2UxOTQ3MjAiLCJ2IjoyfQ]

import Definitions.Def_Yukon_56c3eab949e45c68d9b7d84e

import Definitions.Def_Yukon_be6ea3475ffb6078ec93f154













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingFiberPackingProof6814.S0
open MovingFiberPackingCheck6814 MovingFiberPackingData6814.S0
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem own1_le : shifted 0 own1.toList packed1.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super1_0 : convolution packed0.toList packed1.toList packed1.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem own2_le : shifted 0 own2.toList packed2.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super2_0 : convolution packed0.toList packed2.toList packed2.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super2_1 : convolution packed1.toList packed1.toList packed2.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own3_le : shifted 0 own3.toList packed3.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super3_0 : convolution packed0.toList packed3.toList packed3.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super3_1 : convolution packed1.toList packed2.toList packed3.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own4_le : shifted 0 own4.toList packed4.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super4_0 : convolution packed0.toList packed4.toList packed4.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super4_1 : convolution packed1.toList packed3.toList packed4.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super4_2 : convolution packed2.toList packed2.toList packed4.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own5_le : shifted 0 own5.toList packed5.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super5_0 : convolution packed0.toList packed5.toList packed5.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super5_1 : convolution packed1.toList packed4.toList packed5.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super5_2 : convolution packed2.toList packed3.toList packed5.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own6_le : shifted 0 own6.toList packed6.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super6_0 : convolution packed0.toList packed6.toList packed6.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super6_1 : convolution packed1.toList packed5.toList packed6.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super6_2 : convolution packed2.toList packed4.toList packed6.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super6_3 : convolution packed3.toList packed3.toList packed6.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own7_le : shifted 0 own7.toList packed7.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super7_0 : convolution packed0.toList packed7.toList packed7.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super7_1 : convolution packed1.toList packed6.toList packed7.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super7_2 : convolution packed2.toList packed5.toList packed7.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super7_3 : convolution packed3.toList packed4.toList packed7.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own8_le : shifted 0 own8.toList packed8.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super8_0 : convolution packed0.toList packed8.toList packed8.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super8_1 : convolution packed1.toList packed7.toList packed8.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super8_2 : convolution packed2.toList packed6.toList packed8.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super8_3 : convolution packed3.toList packed5.toList packed8.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super8_4 : convolution packed4.toList packed4.toList packed8.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own9_le : shifted 0 own9.toList packed9.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super9_0 : convolution packed0.toList packed9.toList packed9.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super9_1 : convolution packed1.toList packed8.toList packed9.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super9_2 : convolution packed2.toList packed7.toList packed9.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super9_3 : convolution packed3.toList packed6.toList packed9.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super9_4 : convolution packed4.toList packed5.toList packed9.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own10_le : shifted 0 own10.toList packed10.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super10_0 : convolution packed0.toList packed10.toList packed10.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super10_1 : convolution packed1.toList packed9.toList packed10.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super10_2 : convolution packed2.toList packed8.toList packed10.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super10_3 : convolution packed3.toList packed7.toList packed10.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super10_4 : convolution packed4.toList packed6.toList packed10.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super10_5 : convolution packed5.toList packed5.toList packed10.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own11_le : shifted 0 own11.toList packed11.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super11_0 : convolution packed0.toList packed11.toList packed11.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super11_1 : convolution packed1.toList packed10.toList packed11.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super11_2 : convolution packed2.toList packed9.toList packed11.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super11_3 : convolution packed3.toList packed8.toList packed11.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super11_4 : convolution packed4.toList packed7.toList packed11.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super11_5 : convolution packed5.toList packed6.toList packed11.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own12_le : shifted 0 own12.toList packed12.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super12_0 : convolution packed0.toList packed12.toList packed12.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super12_1 : convolution packed1.toList packed11.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super12_2 : convolution packed2.toList packed10.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super12_3 : convolution packed3.toList packed9.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super12_4 : convolution packed4.toList packed8.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super12_5 : convolution packed5.toList packed7.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super12_6 : convolution packed6.toList packed6.toList packed12.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own13_le : shifted 0 own13.toList packed13.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super13_0 : convolution packed0.toList packed13.toList packed13.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super13_1 : convolution packed1.toList packed12.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super13_2 : convolution packed2.toList packed11.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super13_3 : convolution packed3.toList packed10.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super13_4 : convolution packed4.toList packed9.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super13_5 : convolution packed5.toList packed8.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super13_6 : convolution packed6.toList packed7.toList packed13.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own14_le : shifted 0 own14.toList packed14.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super14_0 : convolution packed0.toList packed14.toList packed14.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super14_1 : convolution packed1.toList packed13.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_2 : convolution packed2.toList packed12.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_3 : convolution packed3.toList packed11.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_4 : convolution packed4.toList packed10.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_5 : convolution packed5.toList packed9.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_6 : convolution packed6.toList packed8.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super14_7 : convolution packed7.toList packed7.toList packed14.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own15_le : shifted 0 own15.toList packed15.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super15_0 : convolution packed0.toList packed15.toList packed15.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super15_1 : convolution packed1.toList packed14.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_2 : convolution packed2.toList packed13.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_3 : convolution packed3.toList packed12.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_4 : convolution packed4.toList packed11.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_5 : convolution packed5.toList packed10.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_6 : convolution packed6.toList packed9.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super15_7 : convolution packed7.toList packed8.toList packed15.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own16_le : shifted 0 own16.toList packed16.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super16_0 : convolution packed0.toList packed16.toList packed16.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super16_1 : convolution packed1.toList packed15.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_2 : convolution packed2.toList packed14.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_3 : convolution packed3.toList packed13.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_4 : convolution packed4.toList packed12.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_5 : convolution packed5.toList packed11.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_6 : convolution packed6.toList packed10.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_7 : convolution packed7.toList packed9.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super16_8 : convolution packed8.toList packed8.toList packed16.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own17_le : shifted 0 own17.toList packed17.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super17_0 : convolution packed0.toList packed17.toList packed17.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super17_1 : convolution packed1.toList packed16.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_2 : convolution packed2.toList packed15.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_3 : convolution packed3.toList packed14.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_4 : convolution packed4.toList packed13.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_5 : convolution packed5.toList packed12.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_6 : convolution packed6.toList packed11.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_7 : convolution packed7.toList packed10.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super17_8 : convolution packed8.toList packed9.toList packed17.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own18_le : shifted 0 own18.toList packed18.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super18_0 : convolution packed0.toList packed18.toList packed18.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super18_1 : convolution packed1.toList packed17.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_2 : convolution packed2.toList packed16.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_3 : convolution packed3.toList packed15.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_4 : convolution packed4.toList packed14.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_5 : convolution packed5.toList packed13.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_6 : convolution packed6.toList packed12.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_7 : convolution packed7.toList packed11.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_8 : convolution packed8.toList packed10.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super18_9 : convolution packed9.toList packed9.toList packed18.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own19_le : shifted 0 own19.toList packed19.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super19_0 : convolution packed0.toList packed19.toList packed19.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super19_1 : convolution packed1.toList packed18.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_2 : convolution packed2.toList packed17.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_3 : convolution packed3.toList packed16.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_4 : convolution packed4.toList packed15.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_5 : convolution packed5.toList packed14.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_6 : convolution packed6.toList packed13.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_7 : convolution packed7.toList packed12.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_8 : convolution packed8.toList packed11.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super19_9 : convolution packed9.toList packed10.toList packed19.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own20_le : shifted 0 own20.toList packed20.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super20_0 : convolution packed0.toList packed20.toList packed20.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super20_1 : convolution packed1.toList packed19.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_2 : convolution packed2.toList packed18.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_3 : convolution packed3.toList packed17.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_4 : convolution packed4.toList packed16.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_5 : convolution packed5.toList packed15.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_6 : convolution packed6.toList packed14.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_7 : convolution packed7.toList packed13.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_8 : convolution packed8.toList packed12.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_9 : convolution packed9.toList packed11.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super20_10 : convolution packed10.toList packed10.toList packed20.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own21_le : shifted 0 own21.toList packed21.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super21_0 : convolution packed0.toList packed21.toList packed21.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super21_1 : convolution packed1.toList packed20.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_2 : convolution packed2.toList packed19.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_3 : convolution packed3.toList packed18.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_4 : convolution packed4.toList packed17.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_5 : convolution packed5.toList packed16.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_6 : convolution packed6.toList packed15.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_7 : convolution packed7.toList packed14.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_8 : convolution packed8.toList packed13.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_9 : convolution packed9.toList packed12.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super21_10 : convolution packed10.toList packed11.toList packed21.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own22_le : shifted 0 own22.toList packed22.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super22_0 : convolution packed0.toList packed22.toList packed22.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super22_1 : convolution packed1.toList packed21.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_2 : convolution packed2.toList packed20.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_3 : convolution packed3.toList packed19.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_4 : convolution packed4.toList packed18.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_5 : convolution packed5.toList packed17.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_6 : convolution packed6.toList packed16.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_7 : convolution packed7.toList packed15.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_8 : convolution packed8.toList packed14.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_9 : convolution packed9.toList packed13.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_10 : convolution packed10.toList packed12.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super22_11 : convolution packed11.toList packed11.toList packed22.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own23_le : shifted 0 own23.toList packed23.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super23_0 : convolution packed0.toList packed23.toList packed23.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super23_1 : convolution packed1.toList packed22.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_2 : convolution packed2.toList packed21.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_3 : convolution packed3.toList packed20.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_4 : convolution packed4.toList packed19.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_5 : convolution packed5.toList packed18.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_6 : convolution packed6.toList packed17.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_7 : convolution packed7.toList packed16.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_8 : convolution packed8.toList packed15.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_9 : convolution packed9.toList packed14.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_10 : convolution packed10.toList packed13.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super23_11 : convolution packed11.toList packed12.toList packed23.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own24_le : shifted 0 own24.toList packed24.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super24_0 : convolution packed0.toList packed24.toList packed24.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super24_1 : convolution packed1.toList packed23.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_2 : convolution packed2.toList packed22.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_3 : convolution packed3.toList packed21.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_4 : convolution packed4.toList packed20.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_5 : convolution packed5.toList packed19.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_6 : convolution packed6.toList packed18.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_7 : convolution packed7.toList packed17.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_8 : convolution packed8.toList packed16.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_9 : convolution packed9.toList packed15.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_10 : convolution packed10.toList packed14.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_11 : convolution packed11.toList packed13.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super24_12 : convolution packed12.toList packed12.toList packed24.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own25_le : shifted 0 own25.toList packed25.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super25_0 : convolution packed0.toList packed25.toList packed25.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super25_1 : convolution packed1.toList packed24.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_2 : convolution packed2.toList packed23.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_3 : convolution packed3.toList packed22.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_4 : convolution packed4.toList packed21.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_5 : convolution packed5.toList packed20.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_6 : convolution packed6.toList packed19.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_7 : convolution packed7.toList packed18.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_8 : convolution packed8.toList packed17.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_9 : convolution packed9.toList packed16.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_10 : convolution packed10.toList packed15.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_11 : convolution packed11.toList packed14.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super25_12 : convolution packed12.toList packed13.toList packed25.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own26_le : shifted 0 own26.toList packed26.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super26_0 : convolution packed0.toList packed26.toList packed26.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super26_1 : convolution packed1.toList packed25.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_2 : convolution packed2.toList packed24.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_3 : convolution packed3.toList packed23.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_4 : convolution packed4.toList packed22.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_5 : convolution packed5.toList packed21.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_6 : convolution packed6.toList packed20.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_7 : convolution packed7.toList packed19.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_8 : convolution packed8.toList packed18.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_9 : convolution packed9.toList packed17.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_10 : convolution packed10.toList packed16.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_11 : convolution packed11.toList packed15.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_12 : convolution packed12.toList packed14.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super26_13 : convolution packed13.toList packed13.toList packed26.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own27_le : shifted 0 own27.toList packed27.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super27_0 : convolution packed0.toList packed27.toList packed27.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super27_1 : convolution packed1.toList packed26.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_2 : convolution packed2.toList packed25.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_3 : convolution packed3.toList packed24.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_4 : convolution packed4.toList packed23.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_5 : convolution packed5.toList packed22.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_6 : convolution packed6.toList packed21.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_7 : convolution packed7.toList packed20.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_8 : convolution packed8.toList packed19.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_9 : convolution packed9.toList packed18.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_10 : convolution packed10.toList packed17.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_11 : convolution packed11.toList packed16.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_12 : convolution packed12.toList packed15.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super27_13 : convolution packed13.toList packed14.toList packed27.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own28_le : shifted 0 own28.toList packed28.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super28_0 : convolution packed0.toList packed28.toList packed28.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super28_1 : convolution packed1.toList packed27.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_2 : convolution packed2.toList packed26.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_3 : convolution packed3.toList packed25.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_4 : convolution packed4.toList packed24.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_5 : convolution packed5.toList packed23.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_6 : convolution packed6.toList packed22.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_7 : convolution packed7.toList packed21.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_8 : convolution packed8.toList packed20.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_9 : convolution packed9.toList packed19.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_10 : convolution packed10.toList packed18.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_11 : convolution packed11.toList packed17.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_12 : convolution packed12.toList packed16.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_13 : convolution packed13.toList packed15.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super28_14 : convolution packed14.toList packed14.toList packed28.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own29_le : shifted 0 own29.toList packed29.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super29_0 : convolution packed0.toList packed29.toList packed29.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super29_1 : convolution packed1.toList packed28.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_2 : convolution packed2.toList packed27.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_3 : convolution packed3.toList packed26.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_4 : convolution packed4.toList packed25.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_5 : convolution packed5.toList packed24.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_6 : convolution packed6.toList packed23.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_7 : convolution packed7.toList packed22.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_8 : convolution packed8.toList packed21.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_9 : convolution packed9.toList packed20.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_10 : convolution packed10.toList packed19.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_11 : convolution packed11.toList packed18.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_12 : convolution packed12.toList packed17.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_13 : convolution packed13.toList packed16.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super29_14 : convolution packed14.toList packed15.toList packed29.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own30_le : shifted 0 own30.toList packed30.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super30_0 : convolution packed0.toList packed30.toList packed30.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super30_1 : convolution packed1.toList packed29.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_2 : convolution packed2.toList packed28.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_3 : convolution packed3.toList packed27.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_4 : convolution packed4.toList packed26.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_5 : convolution packed5.toList packed25.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_6 : convolution packed6.toList packed24.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_7 : convolution packed7.toList packed23.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_8 : convolution packed8.toList packed22.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_9 : convolution packed9.toList packed21.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_10 : convolution packed10.toList packed20.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_11 : convolution packed11.toList packed19.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_12 : convolution packed12.toList packed18.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_13 : convolution packed13.toList packed17.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_14 : convolution packed14.toList packed16.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super30_15 : convolution packed15.toList packed15.toList packed30.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own31_le : shifted 0 own31.toList packed31.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super31_0 : convolution packed0.toList packed31.toList packed31.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super31_1 : convolution packed1.toList packed30.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_2 : convolution packed2.toList packed29.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_3 : convolution packed3.toList packed28.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_4 : convolution packed4.toList packed27.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_5 : convolution packed5.toList packed26.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_6 : convolution packed6.toList packed25.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_7 : convolution packed7.toList packed24.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_8 : convolution packed8.toList packed23.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_9 : convolution packed9.toList packed22.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_10 : convolution packed10.toList packed21.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_11 : convolution packed11.toList packed20.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_12 : convolution packed12.toList packed19.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_13 : convolution packed13.toList packed18.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_14 : convolution packed14.toList packed17.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super31_15 : convolution packed15.toList packed16.toList packed31.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own32_le : shifted 0 own32.toList packed32.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super32_0 : convolution packed0.toList packed32.toList packed32.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super32_1 : convolution packed1.toList packed31.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_2 : convolution packed2.toList packed30.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_3 : convolution packed3.toList packed29.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_4 : convolution packed4.toList packed28.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_5 : convolution packed5.toList packed27.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_6 : convolution packed6.toList packed26.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_7 : convolution packed7.toList packed25.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_8 : convolution packed8.toList packed24.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_9 : convolution packed9.toList packed23.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_10 : convolution packed10.toList packed22.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_11 : convolution packed11.toList packed21.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_12 : convolution packed12.toList packed20.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_13 : convolution packed13.toList packed19.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_14 : convolution packed14.toList packed18.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_15 : convolution packed15.toList packed17.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super32_16 : convolution packed16.toList packed16.toList packed32.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own33_le : shifted 0 own33.toList packed33.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super33_0 : convolution packed0.toList packed33.toList packed33.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super33_1 : convolution packed1.toList packed32.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_2 : convolution packed2.toList packed31.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_3 : convolution packed3.toList packed30.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_4 : convolution packed4.toList packed29.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_5 : convolution packed5.toList packed28.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_6 : convolution packed6.toList packed27.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_7 : convolution packed7.toList packed26.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_8 : convolution packed8.toList packed25.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_9 : convolution packed9.toList packed24.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_10 : convolution packed10.toList packed23.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_11 : convolution packed11.toList packed22.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_12 : convolution packed12.toList packed21.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_13 : convolution packed13.toList packed20.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_14 : convolution packed14.toList packed19.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_15 : convolution packed15.toList packed18.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super33_16 : convolution packed16.toList packed17.toList packed33.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own34_le : shifted 0 own34.toList packed34.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super34_0 : convolution packed0.toList packed34.toList packed34.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super34_1 : convolution packed1.toList packed33.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_2 : convolution packed2.toList packed32.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_3 : convolution packed3.toList packed31.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_4 : convolution packed4.toList packed30.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_5 : convolution packed5.toList packed29.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_6 : convolution packed6.toList packed28.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_7 : convolution packed7.toList packed27.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_8 : convolution packed8.toList packed26.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_9 : convolution packed9.toList packed25.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_10 : convolution packed10.toList packed24.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_11 : convolution packed11.toList packed23.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_12 : convolution packed12.toList packed22.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_13 : convolution packed13.toList packed21.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_14 : convolution packed14.toList packed20.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_15 : convolution packed15.toList packed19.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_16 : convolution packed16.toList packed18.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super34_17 : convolution packed17.toList packed17.toList packed34.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own35_le : shifted 0 own35.toList packed35.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super35_0 : convolution packed0.toList packed35.toList packed35.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super35_1 : convolution packed1.toList packed34.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_2 : convolution packed2.toList packed33.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_3 : convolution packed3.toList packed32.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_4 : convolution packed4.toList packed31.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_5 : convolution packed5.toList packed30.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_6 : convolution packed6.toList packed29.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_7 : convolution packed7.toList packed28.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_8 : convolution packed8.toList packed27.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_9 : convolution packed9.toList packed26.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_10 : convolution packed10.toList packed25.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_11 : convolution packed11.toList packed24.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_12 : convolution packed12.toList packed23.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_13 : convolution packed13.toList packed22.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_14 : convolution packed14.toList packed21.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_15 : convolution packed15.toList packed20.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_16 : convolution packed16.toList packed19.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super35_17 : convolution packed17.toList packed18.toList packed35.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own36_le : shifted 0 own36.toList packed36.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super36_0 : convolution packed0.toList packed36.toList packed36.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super36_1 : convolution packed1.toList packed35.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_2 : convolution packed2.toList packed34.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_3 : convolution packed3.toList packed33.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_4 : convolution packed4.toList packed32.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_5 : convolution packed5.toList packed31.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_6 : convolution packed6.toList packed30.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_7 : convolution packed7.toList packed29.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_8 : convolution packed8.toList packed28.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_9 : convolution packed9.toList packed27.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_10 : convolution packed10.toList packed26.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_11 : convolution packed11.toList packed25.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_12 : convolution packed12.toList packed24.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_13 : convolution packed13.toList packed23.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_14 : convolution packed14.toList packed22.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_15 : convolution packed15.toList packed21.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_16 : convolution packed16.toList packed20.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_17 : convolution packed17.toList packed19.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super36_18 : convolution packed18.toList packed18.toList packed36.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem own37_le : shifted 0 own37.toList packed37.toList=true := by exact shiftedS_sound _ _ _ (by decide +kernel)
theorem super37_0 : convolution packed0.toList packed37.toList packed37.toList=true := by
  exact convolution_zero 176 _ (by exact shiftedS_sound _ _ _ (by decide +kernel))
theorem super37_1 : convolution packed1.toList packed36.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_2 : convolution packed2.toList packed35.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_3 : convolution packed3.toList packed34.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_4 : convolution packed4.toList packed33.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_5 : convolution packed5.toList packed32.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_6 : convolution packed6.toList packed31.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_7 : convolution packed7.toList packed30.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_8 : convolution packed8.toList packed29.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_9 : convolution packed9.toList packed28.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_10 : convolution packed10.toList packed27.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_11 : convolution packed11.toList packed26.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_12 : convolution packed12.toList packed25.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_13 : convolution packed13.toList packed24.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_14 : convolution packed14.toList packed23.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_15 : convolution packed15.toList packed22.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_16 : convolution packed16.toList packed21.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_17 : convolution packed17.toList packed20.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
theorem super37_18 : convolution packed18.toList packed19.toList packed37.toList=true := by exact convolutionS_sound _ _ _ (by decide +kernel)
end ProximityPrize.SubmissionLower.MovingFiberPackingProof6814.S0

namespace ProximityPrize.SubmissionLower.MovingFiberPackingSound6814.S0
open MovingFiberPackingCheck6814 MovingFiberPackingData6814.S0
open MovingFiberPackingProof6814.S0 MovingFiberPackingSemantics6814
set_option autoImplicit false
set_option linter.all false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

theorem own_size (r : Nat) (hr : 1≤r) (hR : r≤37) : (ownRow r).size=176-r := by
  interval_cases r <;> decide +kernel
theorem packed_size (r : Nat) (hR : r≤37) : (packedRow r).size=176-r := by
  interval_cases r <;> decide +kernel
theorem own_under (r : Nat) (hr : 1≤r) (hR : r≤37) : shifted 0 (ownRow r).toList (packedRow r).toList=true := by
  interval_cases r
  · exact own1_le
  · exact own2_le
  · exact own3_le
  · exact own4_le
  · exact own5_le
  · exact own6_le
  · exact own7_le
  · exact own8_le
  · exact own9_le
  · exact own10_le
  · exact own11_le
  · exact own12_le
  · exact own13_le
  · exact own14_le
  · exact own15_le
  · exact own16_le
  · exact own17_le
  · exact own18_le
  · exact own19_le
  · exact own20_le
  · exact own21_le
  · exact own22_le
  · exact own23_le
  · exact own24_le
  · exact own25_le
  · exact own26_le
  · exact own27_le
  · exact own28_le
  · exact own29_le
  · exact own30_le
  · exact own31_le
  · exact own32_le
  · exact own33_le
  · exact own34_le
  · exact own35_le
  · exact own36_le
  · exact own37_le
theorem all_checks (R r : Nat) (hrr : 2*r≤R) (hR : R≤37) :
    convolution (packedRow r).toList (packedRow (R-r)).toList (packedRow R).toList=true := by
  have hrmax : r≤R/2 := (Nat.le_div_iff_mul_le (by decide : 0<2)).mpr (by omega)
  interval_cases R
  · interval_cases r
    · exact convolutionS_sound _ _ _ (by decide +kernel)
  · interval_cases r
    · exact super1_0
  · interval_cases r
    · exact super2_0
    · exact super2_1
  · interval_cases r
    · exact super3_0
    · exact super3_1
  · interval_cases r
    · exact super4_0
    · exact super4_1
    · exact super4_2
  · interval_cases r
    · exact super5_0
    · exact super5_1
    · exact super5_2
  · interval_cases r
    · exact super6_0
    · exact super6_1
    · exact super6_2
    · exact super6_3
  · interval_cases r
    · exact super7_0
    · exact super7_1
    · exact super7_2
    · exact super7_3
  · interval_cases r
    · exact super8_0
    · exact super8_1
    · exact super8_2
    · exact super8_3
    · exact super8_4
  · interval_cases r
    · exact super9_0
    · exact super9_1
    · exact super9_2
    · exact super9_3
    · exact super9_4
  · interval_cases r
    · exact super10_0
    · exact super10_1
    · exact super10_2
    · exact super10_3
    · exact super10_4
    · exact super10_5
  · interval_cases r
    · exact super11_0
    · exact super11_1
    · exact super11_2
    · exact super11_3
    · exact super11_4
    · exact super11_5
  · interval_cases r
    · exact super12_0
    · exact super12_1
    · exact super12_2
    · exact super12_3
    · exact super12_4
    · exact super12_5
    · exact super12_6
  · interval_cases r
    · exact super13_0
    · exact super13_1
    · exact super13_2
    · exact super13_3
    · exact super13_4
    · exact super13_5
    · exact super13_6
  · interval_cases r
    · exact super14_0
    · exact super14_1
    · exact super14_2
    · exact super14_3
    · exact super14_4
    · exact super14_5
    · exact super14_6
    · exact super14_7
  · interval_cases r
    · exact super15_0
    · exact super15_1
    · exact super15_2
    · exact super15_3
    · exact super15_4
    · exact super15_5
    · exact super15_6
    · exact super15_7
  · interval_cases r
    · exact super16_0
    · exact super16_1
    · exact super16_2
    · exact super16_3
    · exact super16_4
    · exact super16_5
    · exact super16_6
    · exact super16_7
    · exact super16_8
  · interval_cases r
    · exact super17_0
    · exact super17_1
    · exact super17_2
    · exact super17_3
    · exact super17_4
    · exact super17_5
    · exact super17_6
    · exact super17_7
    · exact super17_8
  · interval_cases r
    · exact super18_0
    · exact super18_1
    · exact super18_2
    · exact super18_3
    · exact super18_4
    · exact super18_5
    · exact super18_6
    · exact super18_7
    · exact super18_8
    · exact super18_9
  · interval_cases r
    · exact super19_0
    · exact super19_1
    · exact super19_2
    · exact super19_3
    · exact super19_4
    · exact super19_5
    · exact super19_6
    · exact super19_7
    · exact super19_8
    · exact super19_9
  · interval_cases r
    · exact super20_0
    · exact super20_1
    · exact super20_2
    · exact super20_3
    · exact super20_4
    · exact super20_5
    · exact super20_6
    · exact super20_7
    · exact super20_8
    · exact super20_9
    · exact super20_10
  · interval_cases r
    · exact super21_0
    · exact super21_1
    · exact super21_2
    · exact super21_3
    · exact super21_4
    · exact super21_5
    · exact super21_6
    · exact super21_7
    · exact super21_8
    · exact super21_9
    · exact super21_10
  · interval_cases r
    · exact super22_0
    · exact super22_1
    · exact super22_2
    · exact super22_3
    · exact super22_4
    · exact super22_5
    · exact super22_6
    · exact super22_7
    · exact super22_8
    · exact super22_9
    · exact super22_10
    · exact super22_11
  · interval_cases r
    · exact super23_0
    · exact super23_1
    · exact super23_2
    · exact super23_3
    · exact super23_4
    · exact super23_5
    · exact super23_6
    · exact super23_7
    · exact super23_8
    · exact super23_9
    · exact super23_10
    · exact super23_11
  · interval_cases r
    · exact super24_0
    · exact super24_1
    · exact super24_2
    · exact super24_3
    · exact super24_4
    · exact super24_5
    · exact super24_6
    · exact super24_7
    · exact super24_8
    · exact super24_9
    · exact super24_10
    · exact super24_11
    · exact super24_12
  · interval_cases r
    · exact super25_0
    · exact super25_1
    · exact super25_2
    · exact super25_3
    · exact super25_4
    · exact super25_5
    · exact super25_6
    · exact super25_7
    · exact super25_8
    · exact super25_9
    · exact super25_10
    · exact super25_11
    · exact super25_12
  · interval_cases r
    · exact super26_0
    · exact super26_1
    · exact super26_2
    · exact super26_3
    · exact super26_4
    · exact super26_5
    · exact super26_6
    · exact super26_7
    · exact super26_8
    · exact super26_9
    · exact super26_10
    · exact super26_11
    · exact super26_12
    · exact super26_13
  · interval_cases r
    · exact super27_0
    · exact super27_1
    · exact super27_2
    · exact super27_3
    · exact super27_4
    · exact super27_5
    · exact super27_6
    · exact super27_7
    · exact super27_8
    · exact super27_9
    · exact super27_10
    · exact super27_11
    · exact super27_12
    · exact super27_13
  · interval_cases r
    · exact super28_0
    · exact super28_1
    · exact super28_2
    · exact super28_3
    · exact super28_4
    · exact super28_5
    · exact super28_6
    · exact super28_7
    · exact super28_8
    · exact super28_9
    · exact super28_10
    · exact super28_11
    · exact super28_12
    · exact super28_13
    · exact super28_14
  · interval_cases r
    · exact super29_0
    · exact super29_1
    · exact super29_2
    · exact super29_3
    · exact super29_4
    · exact super29_5
    · exact super29_6
    · exact super29_7
    · exact super29_8
    · exact super29_9
    · exact super29_10
    · exact super29_11
    · exact super29_12
    · exact super29_13
    · exact super29_14
  · interval_cases r
    · exact super30_0
    · exact super30_1
    · exact super30_2
    · exact super30_3
    · exact super30_4
    · exact super30_5
    · exact super30_6
    · exact super30_7
    · exact super30_8
    · exact super30_9
    · exact super30_10
    · exact super30_11
    · exact super30_12
    · exact super30_13
    · exact super30_14
    · exact super30_15
  · interval_cases r
    · exact super31_0
    · exact super31_1
    · exact super31_2
    · exact super31_3
    · exact super31_4
    · exact super31_5
    · exact super31_6
    · exact super31_7
    · exact super31_8
    · exact super31_9
    · exact super31_10
    · exact super31_11
    · exact super31_12
    · exact super31_13
    · exact super31_14
    · exact super31_15
  · interval_cases r
    · exact super32_0
    · exact super32_1
    · exact super32_2
    · exact super32_3
    · exact super32_4
    · exact super32_5
    · exact super32_6
    · exact super32_7
    · exact super32_8
    · exact super32_9
    · exact super32_10
    · exact super32_11
    · exact super32_12
    · exact super32_13
    · exact super32_14
    · exact super32_15
    · exact super32_16
  · interval_cases r
    · exact super33_0
    · exact super33_1
    · exact super33_2
    · exact super33_3
    · exact super33_4
    · exact super33_5
    · exact super33_6
    · exact super33_7
    · exact super33_8
    · exact super33_9
    · exact super33_10
    · exact super33_11
    · exact super33_12
    · exact super33_13
    · exact super33_14
    · exact super33_15
    · exact super33_16
  · interval_cases r
    · exact super34_0
    · exact super34_1
    · exact super34_2
    · exact super34_3
    · exact super34_4
    · exact super34_5
    · exact super34_6
    · exact super34_7
    · exact super34_8
    · exact super34_9
    · exact super34_10
    · exact super34_11
    · exact super34_12
    · exact super34_13
    · exact super34_14
    · exact super34_15
    · exact super34_16
    · exact super34_17
  · interval_cases r
    · exact super35_0
    · exact super35_1
    · exact super35_2
    · exact super35_3
    · exact super35_4
    · exact super35_5
    · exact super35_6
    · exact super35_7
    · exact super35_8
    · exact super35_9
    · exact super35_10
    · exact super35_11
    · exact super35_12
    · exact super35_13
    · exact super35_14
    · exact super35_15
    · exact super35_16
    · exact super35_17
  · interval_cases r
    · exact super36_0
    · exact super36_1
    · exact super36_2
    · exact super36_3
    · exact super36_4
    · exact super36_5
    · exact super36_6
    · exact super36_7
    · exact super36_8
    · exact super36_9
    · exact super36_10
    · exact super36_11
    · exact super36_12
    · exact super36_13
    · exact super36_14
    · exact super36_15
    · exact super36_16
    · exact super36_17
    · exact super36_18
  · interval_cases r
    · exact super37_0
    · exact super37_1
    · exact super37_2
    · exact super37_3
    · exact super37_4
    · exact super37_5
    · exact super37_6
    · exact super37_7
    · exact super37_8
    · exact super37_9
    · exact super37_10
    · exact super37_11
    · exact super37_12
    · exact super37_13
    · exact super37_14
    · exact super37_15
    · exact super37_16
    · exact super37_17
    · exact super37_18
theorem bellman : AffineFactorAggregate6808.BellmanRows 37 175 own packed :=
  symmetric_bellman ownRow packedRow own_size packed_size own_under all_checks


end ProximityPrize.SubmissionLower.MovingFiberPackingSound6814.S0


