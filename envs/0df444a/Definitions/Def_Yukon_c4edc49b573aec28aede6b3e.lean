-- Prove2me | Definitions.Def_Yukon_c4edc49b573aec28aede6b3e
-- name    : Yukon_c4edc49b573aec28aede6b3e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T13:47:37.55599+00:00
-- url     : https://prove2.me/theorems/81a6a8ca-8bd3-4713-b336-da5aec938154
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCertR11B52T3910To3939Fast.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR11B52T3910To3939Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR11B52T3910To3939Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR11B52T3910To3939Fast.lean
--
--   yukon-proof-operation:foundation-direct-b7b62c639fc1ccf716c9303cbc741dac5ad05066b3a1f4a3faffe890f69d9bb3
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmFmYjc2NzdjMDU2YmIxNDZhYTg1MzljMzljMmNiZThhNTBlODg2MDY4Mzg2NTliODU0MmNkNjExM2U4NmVhOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LWI3YjYyYzYzOWZjMWNjZjcxNmM5MzAzY2JjNzQxZGFjNWFkMDUwNjZiM2ExZjRhM2ZhZmZlODkwZjY5ZDliYjMiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9jNGVkYzQ5YjU3M2FlYzI4YWVkZTZiM2UiLCJ2IjoyfQ]

import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_5632b366dda2ee86d6d6c66d











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 885ee5cdc24340c6a794d4b7391c6080cfd0ecd23e9e225ebe0e1721fe54b5e6.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR11B52T3910To3939Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def band : Band := ⟨11,52,3910,3939,15557768288906582⟩

def p1 (l h x y u:Nat):Rectangle:=⟨l,h,4134,1,1270,x,y,u⟩
def p2 (l h x y u:Nat):Rectangle:=⟨l,h,8268,2,2540,x,y,u⟩
def p4 (l h x y u:Nat):Rectangle:=⟨l,h,16536,4,5080,x,y,u⟩
def p8 (l h x y u:Nat):Rectangle:=⟨l,h,33072,8,10160,x,y,u⟩
def p206 (l h x y u:Nat):Rectangle:=⟨l,h,41768,250,10158,x,y,u⟩
def r0:=p1 6815681 6957968 10358 10412 5665
def r1:=p1 6957969 7100255 10356 10417 5664
def r2:=p1 7100256 7242543 10353 10415 5663
def r3:=p1 7242544 7384830 10350 10411 5662
def r4:=p1 7384831 7527118 10346 10407 5661
def r5:=p2 7527119 7669405 16731 16822 11320
def r6:=p1 7669406 7740549 10354 10416 5659
def r7:=p1 7740550 7811693 10351 10413 5658
def r8:=p1 7811694 7882837 10349 10410 5658
def r9:=p1 7882838 7953980 10348 10408 5657
def r10:=p2 7953981 8025124 16733 16825 11314
def r11:=p1 8025125 8060696 10350 10412 5656
def r12:=p1 8060697 8096268 10349 10411 5656
def r13:=p1 8096269 8131840 10349 10410 5656
def r14:=p2 8131841 8167412 16735 16830 11311
def r15:=p2 8167413 8202984 16734 16826 11311
def r16:=p4 8202985 8238555 29504 29662 22620
def r17:=p2 8238556 8256341 16735 16831 11309
def r18:=p2 8256342 8274127 16735 16829 11309
def r19:=p2 8274128 8291913 16735 16828 11309
def r20:=p4 8291914 8309699 29505 29668 22618
def r21:=p4 8309700 8327485 29505 29663 22617
def r22:=p2 8327486 8336378 16735 16828 11308
def r23:=p4 8336379 8345271 29506 29671 22616
def r24:=p4 8345272 8354164 29506 29668 22616
def r25:=p4 8354165 8363057 29505 29666 22616
def r26:=p8 8363058 8371950 55047 55304 45232
def r27:=p8 8371951 8380843 55047 55311 45231
def r28:=p206 8380844 8389736 3027562 3039894 42024
def r29:=p206 8389737 8398629 3021554 3034663 42007
def r30:=p206 8398630 8407522 3016882 3030653 41990
def r31:=p206 8407523 8416415 3013264 3027608 41973
def r32:=p206 8416416 8425308 3010493 3025336 41956
def r33:=p206 8425309 8434201 3008414 3023698 41939
def r34:=p206 8434202 8443094 3006907 3022582 41922
def r35:=p206 8443095 8451987 3005875 3021901 41906
def r36:=p206 8451988 8460880 3005246 3021588 41889
def r37:=p206 8460881 8469773 3004962 3021591 41872
def r38:=p206 8469774 8478666 3004976 3021867 41855
def r39:=p206 8478667 8487559 3005248 3022380 41838
def r40:=p206 8487560 8496452 3005747 3023100 41821
def r41:=p206 8496453 8505345 3006446 3024003 41804
def r42:=p206 8505346 8514238 3007320 3025068 41787
def r43:=p206 8514239 8523130 3008312 3026238 41770
def r44:=p206 8523131 8532023 3009522 3027614 41753
def r45:=p206 8532024 8540916 3010819 3029067 41736
def r46:=p206 8540917 8549809 3012230 3030625 41719
def r47:=p206 8549810 8558702 3013745 3032277 41702
def r48:=p206 8558703 8567595 3015353 3034017 41685
def r49:=p206 8567596 8576488 3017048 3035835 41668
def r50:=p206 8576489 8585381 3018821 3037727 41651
def r51:=p206 8585382 8594274 3020666 3039685 41634
def r52:=p206 8594275 8603167 3022579 3041705 41617
def r53:=p206 8603168 8612060 3024554 3043782 41600
def r54:=p206 8612061 8620953 3026586 3045913 41583
def r55:=p206 8620954 8629846 3028673 3048094 41566
def r56:=p206 8629847 8638739 3030811 3050323 41549
def r57:=p206 8638740 8647632 3032997 3052596 41532
def r58:=p206 8647633 8656525 3035227 3054910 41515
def r59:=p206 8656526 8665418 3038615 3057263 41498
def r60:=p206 8665419 8674311 3042899 3060390 41481
def r61:=p206 8674312 8683204 3047095 3064818 41464
def r62:=p206 8683205 8692097 3051211 3069151 41448
def r63:=p206 8692098 8700990 3055259 3073402 41431
def r64:=p206 8700991 8709883 3059249 3077581 41414
def r65:=p206 8709884 8718776 3063187 3081697 41397
def r66:=p206 8718777 8727669 3067080 3085757 41380
def r67:=p206 8727670 8736562 3070933 3089768 41363
def r68:=p206 8736563 8745455 3074750 3093735 41346
def r69:=p206 8745456 8754348 3078536 3097663 41329
def r70:=p206 8754349 8763241 3082295 3101556 41312
def r71:=p206 8763242 8772134 3086028 3105418 41295
def r72:=p206 8772135 8781027 3089740 3109253 41278
def r73:=p206 8781028 8789920 3093432 3113062 41261
def r74:=p206 8789921 8798813 3097107 3116850 41244
def r75:=p206 8798814 8807705 3100738 3120589 41227
def r76:=p206 8807706 8816598 3104412 3124367 41210
def r77:=p206 8816599 8825491 3108047 3128102 41193
def r78:=p206 8825492 8834384 3111672 3131823 41176
def r79:=p206 8834385 8843277 3115287 3135531 41159
def r80:=p206 8843278 8852170 3118895 3139229 41142
def r81:=p206 8852171 8861063 3122497 3142918 41125
def r82:=p206 8861064 8869956 3126092 3146598 41108
def r83:=p206 8869957 8878849 3129684 3150271 41091
def r84:=p206 8878850 8887742 3133271 3153938 41074
def r85:=p206 8887743 8896635 3136856 3157600 41057
def r86:=p206 8896636 8905528 3140438 3161258 41040
def r87:=p206 8905529 8914421 3144019 3164912 41023
def r88:=p206 8914422 8923314 3147598 3168563 41007
def r89:=p206 8923315 8932207 3151176 3172211 40990
def r90:=p206 8932208 8941100 3154755 3175858 40973
def r91:=p206 8941101 8949993 3158335 3179505 40956
def r92:=p206 8949994 8958886 3161917 3183152 40939
def r93:=p206 8958887 8967779 3165500 3186799 40922
def r94:=p206 8967780 8976672 3169085 3190446 40905
def r95:=p206 8976673 8985565 3172672 3194095 40888
def r96:=p206 8985566 8994458 3177834 3198230 40871
def r97:=p206 8994459 9003351 3183228 3203739 40854
def r98:=p206 9003352 9012244 3188547 3209169 40837
def r99:=p206 9012245 9021137 3193797 3214525 40820
def r100:=p206 9021138 9030030 3198983 3219814 40803
def r101:=p206 9030031 9038923 3204110 3225041 40786
def r102:=p206 9038924 9047816 3209182 3230210 40769
def r103:=p206 9047817 9056709 3214204 3235326 40752
def r104:=p206 9056710 9065602 3219180 3240392 40735
def r105:=p206 9065603 9074495 3224112 3245413 40718
def r106:=p206 9074496 9092280 3664484 3676852 40701
def r107:=p206 9092281 9110066 3636340 3651103 40667
def r108:=p206 9110067 9127852 3619131 3635586 40633
def r109:=p206 9127853 9145638 3608678 3626399 40599
def r110:=p206 9145639 9163424 3602638 3621347 40566
def r111:=p206 9163425 9181210 3599659 3619164 40532
def r112:=p206 9181211 9198996 3598898 3619063 40498
def r113:=p206 9198997 9216782 3599799 3620521 40464
def r114:=p206 9216783 9234568 3601980 3623182 40430
def r115:=p206 9234569 9252354 3605177 3626798 40396
def r116:=p206 9252355 9270140 3609192 3631184 40362
def r117:=p206 9270141 9287926 3613874 3636200 40328
def r118:=p206 9287927 9305712 3619114 3641740 40294
def r119:=p206 9305713 9323498 3624826 3647727 40260
def r120:=p206 9323499 9341284 3630943 3654097 40226
def r121:=p206 9341285 9359070 3637412 3660800 40192
def r122:=p206 9359071 9376855 3644154 3667761 40158
def r123:=p206 9376856 9394641 3651240 3675053 40124
def r124:=p206 9394642 9412427 3658531 3682537 40091
def r125:=p206 9412428 9430213 3666045 3690235 40057
def r126:=p206 9430214 9447999 3673764 3698127 40023
def r127:=p206 9448000 9465785 3681669 3706200 39989
def r128:=p206 9465786 9483571 3689748 3714439 39955
def r129:=p206 9483572 9501357 3699627 3722965 39921
def r130:=p206 9501358 9519143 3712513 3736155 39887
def r131:=p206 9519144 9536929 3725198 3749122 39853
def r132:=p206 9536930 9554715 3737725 3761912 39819
def r133:=p206 9554716 9572501 3750122 3774556 39785
def r134:=p206 9572502 9590287 3762414 3787080 39751
def r135:=p206 9590288 9608073 3774622 3799508 39717
def r136:=p206 9608074 9625859 3786764 3811859 39683
def r137:=p206 9625860 9643645 3798851 3824146 39650
def r138:=p206 9643646 9661430 3810873 3836359 39616
def r139:=p206 9661431 9679216 3822934 3848604 39582
def r140:=p206 9679217 9697002 3834953 3860801 39548
def r141:=p206 9697003 9714788 3846970 3872989 39514
def r142:=p206 9714789 9732574 3858991 3885177 39480
def r143:=p206 9732575 9750360 3871026 3897373 39446
def r144:=p206 9750361 9768146 3883079 3909584 39412
def r145:=p206 9768147 9785932 3895157 3921816 39378
def r146:=p206 9785933 9803718 3907265 3934074 39344
def r147:=p206 9803719 9821504 3919408 3946364 39310
def r148:=p206 9821505 9839290 3936279 3962590 39276
def r149:=p206 9839291 9857076 3952920 3979450 39242
def r150:=p206 9857077 9874862 3969352 3996094 39209
def r151:=p206 9874863 9892648 3985610 4012556 39175
def r152:=p206 9892649 9910434 4001720 4028865 39141
def r153:=p206 9910435 9928220 4017706 4045043 39107
def r154:=p206 9928221 9946005 4033558 4061083 39073
def r155:=p206 9946006 9963791 4049381 4077088 39039
def r156:=p206 9963792 9981577 4065106 4092992 39005
def r157:=p206 9981578 9999363 4080775 4108836 38971
def r158:=p206 9999364 10017149 4096402 4124634 38937
def r159:=p206 10017150 10052721 5187930 5214166 38903
def r160:=p206 10052722 10088293 5123809 5152041 38835
def r161:=p206 10088294 10123865 5093834 5123474 38768
def r162:=p206 10123866 10159437 5083422 5114142 38700
def r163:=p206 10159438 10195009 5085400 5116997 38632
def r164:=p206 10195010 10230580 5095718 5128060 38564
def r165:=p206 10230581 10266152 5112256 5145253 38496
def r166:=p206 10266153 10301724 5133300 5166889 38428
def r167:=p206 10301725 10337296 5157949 5192082 38360
def r168:=p206 10337297 10372868 5185527 5220170 38293
def r169:=p206 10372869 10408440 5215595 5250723 38225
def r170:=p206 10408441 10444012 5247818 5283411 38157
def r171:=p206 10444013 10479584 5286175 5320745 38089
def r172:=p206 10479585 10515155 5336842 5372145 38021
def r173:=p206 10515156 10550727 5387921 5423905 37953
def r174:=p206 10550728 10586299 5439349 5475976 37885
def r175:=p206 10586300 10621871 5491336 5528575 37818
def r176:=p206 10621872 10657443 5543996 5581825 37750
def r177:=p206 10657444 10693015 5597419 5635820 37682
def r178:=p206 10693016 10728587 5651681 5690642 37614
def r179:=p206 10728588 10764159 5706853 5746364 37546
def r180:=p206 10764160 10799730 5762965 5803018 37478
def r181:=p206 10799731 10835302 5825819 5865568 37411
def r182:=p206 10835303 10870874 5901495 5941981 37343
def r183:=p206 10870875 10906446 5977204 6018410 37275
def r184:=p206 10906447 10942018 6053208 6095119 37207
def r185:=p206 10942019 10977590 6129730 6172336 37139
def r186:=p206 10977591 11013162 6206962 6250258 37071
def r187:=p206 11013163 11048734 6285065 6329045 37003
def r188:=p206 11048735 11084305 6364156 6408820 36936
def r189:=p206 11084306 11119877 6444543 6489892 36868
def r190:=p206 11119878 11155449 6541391 6586863 36800
def r191:=p206 11155450 11191021 6644795 6691150 36732
def r192:=p206 11191022 11226593 6748995 6796230 36664
def r193:=p206 11226594 11297737 13761861 13830223 36596
def r194:=p206 11297738 11368880 12934521 13009296 36461

def b0 : List (Rectangle × FastWitness) := [(r0,⟨63,48,54⟩),(r1,⟨63,51,53⟩),(r2,⟨63,48,52⟩),(r3,⟨63,45,48⟩),(r4,⟨63,41,44⟩),(r5,⟨63,42,45⟩),(r6,⟨63,49,52⟩),(r7,⟨63,46,50⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨63,44,47⟩),(r9,⟨63,43,45⟩),(r10,⟨63,44,47⟩),(r11,⟨63,45,49⟩),(r12,⟨63,44,48⟩),(r13,⟨63,44,47⟩),(r14,⟨63,45,51⟩),(r15,⟨63,45,48⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨63,45,52⟩),(r17,⟨63,45,52⟩),(r18,⟨63,45,51⟩),(r19,⟨63,45,50⟩),(r20,⟨63,46,55⟩),(r21,⟨63,46,52⟩),(r22,⟨63,45,50⟩),(r23,⟨63,46,57⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨63,46,55⟩),(r25,⟨63,46,54⟩),(r26,⟨63,43,47⟩),(r27,⟨63,45,47⟩),(r28,⟨63,46,46⟩),(r29,⟨63,46,46⟩),(r30,⟨63,46,46⟩),(r31,⟨63,46,46⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨63,46,46⟩),(r33,⟨63,46,46⟩),(r34,⟨63,46,46⟩),(r35,⟨63,46,46⟩),(r36,⟨63,46,46⟩),(r37,⟨63,46,46⟩),(r38,⟨63,46,46⟩),(r39,⟨63,46,46⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨63,46,46⟩),(r41,⟨63,46,46⟩),(r42,⟨63,46,46⟩),(r43,⟨63,46,46⟩),(r44,⟨63,46,46⟩),(r45,⟨63,46,46⟩),(r46,⟨63,46,46⟩),(r47,⟨63,46,46⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨63,46,46⟩),(r49,⟨63,46,46⟩),(r50,⟨63,46,46⟩),(r51,⟨63,46,46⟩),(r52,⟨63,46,46⟩),(r53,⟨63,46,46⟩),(r54,⟨63,46,46⟩),(r55,⟨63,46,46⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨63,46,46⟩),(r57,⟨63,46,46⟩),(r58,⟨63,46,46⟩),(r59,⟨63,46,47⟩),(r60,⟨63,47,47⟩),(r61,⟨63,47,47⟩),(r62,⟨63,47,47⟩),(r63,⟨63,47,47⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨63,47,47⟩),(r65,⟨63,47,47⟩),(r66,⟨63,47,47⟩),(r67,⟨63,47,47⟩),(r68,⟨63,47,47⟩),(r69,⟨63,47,47⟩),(r70,⟨63,47,47⟩),(r71,⟨63,47,47⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨63,47,47⟩),(r73,⟨63,47,47⟩),(r74,⟨63,47,47⟩),(r75,⟨63,47,47⟩),(r76,⟨63,47,47⟩),(r77,⟨63,47,47⟩),(r78,⟨63,47,47⟩),(r79,⟨63,47,47⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨63,47,47⟩),(r81,⟨63,47,47⟩),(r82,⟨63,47,47⟩),(r83,⟨63,47,47⟩),(r84,⟨63,47,47⟩),(r85,⟨63,47,47⟩),(r86,⟨63,47,47⟩),(r87,⟨63,47,47⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨63,47,47⟩),(r89,⟨63,47,47⟩),(r90,⟨63,47,47⟩),(r91,⟨63,47,47⟩),(r92,⟨63,47,47⟩),(r93,⟨63,47,47⟩),(r94,⟨63,47,47⟩),(r95,⟨63,47,47⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨63,48,48⟩),(r97,⟨63,48,48⟩),(r98,⟨63,48,48⟩),(r99,⟨63,48,48⟩),(r100,⟨63,48,48⟩),(r101,⟨63,48,48⟩),(r102,⟨63,48,48⟩),(r103,⟨63,48,48⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨63,48,48⟩),(r105,⟨63,48,48⟩),(r106,⟨63,50,50⟩),(r107,⟨63,50,50⟩),(r108,⟨63,50,50⟩),(r109,⟨63,50,50⟩),(r110,⟨63,50,50⟩),(r111,⟨63,50,50⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨63,50,50⟩),(r113,⟨63,50,50⟩),(r114,⟨63,50,50⟩),(r115,⟨63,50,50⟩),(r116,⟨63,50,50⟩),(r117,⟨63,50,50⟩),(r118,⟨63,50,50⟩),(r119,⟨63,50,50⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨63,50,50⟩),(r121,⟨63,50,50⟩),(r122,⟨63,50,50⟩),(r123,⟨63,50,50⟩),(r124,⟨63,50,50⟩),(r125,⟨63,50,50⟩),(r126,⟨63,50,50⟩),(r127,⟨63,50,50⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨63,50,50⟩),(r129,⟨63,51,51⟩),(r130,⟨63,51,51⟩),(r131,⟨63,51,51⟩),(r132,⟨63,51,51⟩),(r133,⟨63,51,51⟩),(r134,⟨63,51,51⟩),(r135,⟨63,51,51⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨63,51,51⟩),(r137,⟨63,51,51⟩),(r138,⟨63,51,51⟩),(r139,⟨63,51,51⟩),(r140,⟨63,51,51⟩),(r141,⟨63,51,51⟩),(r142,⟨63,51,51⟩),(r143,⟨63,51,51⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨63,51,51⟩),(r145,⟨63,51,51⟩),(r146,⟨63,51,51⟩),(r147,⟨63,51,52⟩),(r148,⟨63,52,52⟩),(r149,⟨63,52,52⟩),(r150,⟨63,52,52⟩),(r151,⟨63,52,52⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨63,52,52⟩),(r153,⟨63,52,52⟩),(r154,⟨63,52,52⟩),(r155,⟨63,52,52⟩),(r156,⟨63,52,52⟩),(r157,⟨63,52,52⟩),(r158,⟨63,52,52⟩),(r159,⟨63,55,55⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨63,55,55⟩),(r161,⟨63,55,55⟩),(r162,⟨63,55,55⟩),(r163,⟨63,55,55⟩),(r164,⟨63,55,55⟩),(r165,⟨63,55,55⟩),(r166,⟨63,55,55⟩),(r167,⟨63,55,55⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨63,55,55⟩),(r169,⟨63,55,55⟩),(r170,⟨63,55,55⟩),(r171,⟨63,56,56⟩),(r172,⟨63,56,56⟩),(r173,⟨63,56,56⟩),(r174,⟨63,56,56⟩),(r175,⟨63,56,56⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨63,56,56⟩),(r177,⟨63,56,56⟩),(r178,⟨63,56,56⟩),(r179,⟨63,56,56⟩),(r180,⟨63,56,56⟩),(r181,⟨63,57,57⟩),(r182,⟨63,57,57⟩),(r183,⟨63,57,57⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨63,57,57⟩),(r185,⟨63,57,57⟩),(r186,⟨63,57,57⟩),(r187,⟨63,57,57⟩),(r188,⟨63,57,57⟩),(r189,⟨63,57,57⟩),(r190,⟨63,58,58⟩),(r191,⟨63,58,58⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨63,58,58⟩),(r193,⟨63,62,62⟩),(r194,⟨63,62,62⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24
def rows : List Rectangle := witnessedRows.map Prod.fst
theorem all_fast_checked : fastCheckList band witnessedRows=true := by
  have joinChecked (xs ys : List (Rectangle × FastWitness)) (hx : fastCheckList band xs = true) (hy : fastCheckList band ys = true) : fastCheckList band (xs ++ ys) = true := by
    rw [fastCheckList_append, hx, hy]
    rfl
  have joined1 := joinChecked _ _ checked0 checked1
  have joined2 := joinChecked _ _ joined1 checked2
  have joined3 := joinChecked _ _ joined2 checked3
  have joined4 := joinChecked _ _ joined3 checked4
  have joined5 := joinChecked _ _ joined4 checked5
  have joined6 := joinChecked _ _ joined5 checked6
  have joined7 := joinChecked _ _ joined6 checked7
  have joined8 := joinChecked _ _ joined7 checked8
  have joined9 := joinChecked _ _ joined8 checked9
  have joined10 := joinChecked _ _ joined9 checked10
  have joined11 := joinChecked _ _ joined10 checked11
  have joined12 := joinChecked _ _ joined11 checked12
  have joined13 := joinChecked _ _ joined12 checked13
  have joined14 := joinChecked _ _ joined13 checked14
  have joined15 := joinChecked _ _ joined14 checked15
  have joined16 := joinChecked _ _ joined15 checked16
  have joined17 := joinChecked _ _ joined16 checked17
  have joined18 := joinChecked _ _ joined17 checked18
  have joined19 := joinChecked _ _ joined18 checked19
  have joined20 := joinChecked _ _ joined19 checked20
  have joined21 := joinChecked _ _ joined20 checked21
  have joined22 := joinChecked _ _ joined21 checked22
  have joined23 := joinChecked _ _ joined22 checked23
  have joined24 := joinChecked _ _ joined23 checked24
  exact joined24
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR11B52T3910To3939Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 11)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 11≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤52)
    (hT0 : 3910≤T) (hT1 : T≤3939) (hnu : 6815681≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤15557768288906582 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR11B52T3910To3939Fast


