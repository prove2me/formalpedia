-- Prove2me | Definitions.Def_Yukon_98750b4547ad3814dbd721e7
-- name    : Yukon_98750b4547ad3814dbd721e7
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T11:26:45.380151+00:00
-- url     : https://prove2.me/theorems/a85aaf3f-4e3c-42c2-8118-78a1136b062d
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCertR10B56T3902To3917Fast.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR10B56T3902To3917Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR10B56T3902To3917Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR10B56T3902To3917Fast.lean
--
--   yukon-proof-operation:foundation-direct-34f33ad8ffa88c2fe6bb20b19e2d54a62bc08c4d8b50666b89830949dd412a6a
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMGMwYTNiNGNiOTljMmEzZTdkNmY3ZjA1NGU0YzY3MDYzNjJlNWNhN2RjNWQ2NmRiZTdmYzFiZmY3MTQ1ZmE3YiIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmZvdW5kYXRpb24tZGlyZWN0LTM0ZjMzYWQ4ZmZhODhjMmZlNmJiMjBiMTllMmQ1NGE2MmJjMDhjNGQ4YjUwNjY2Yjg5ODMwOTQ5ZGQ0MTJhNmEiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl85ODc1MGI0NTQ3YWQzODE0ZGJkNzIxZTciLCJ2IjoyfQ]

import Definitions.Def_Yukon_e757298719adf05c20287f89











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: 4b6b84fd2d09e94925d822f5f70dec1e092013a39b6490b4a5c3b8f6d9179815.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR10B56T3902To3917Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def band : Band := ⟨10,56,3902,3917,12314372801839158⟩

def p1 (l h x y u:Nat):Rectangle:=⟨l,h,4134,1,1270,x,y,u⟩
def p2 (l h x y u:Nat):Rectangle:=⟨l,h,8268,2,2540,x,y,u⟩
def p4 (l h x y u:Nat):Rectangle:=⟨l,h,16536,4,5080,x,y,u⟩
def p8 (l h x y u:Nat):Rectangle:=⟨l,h,33072,8,10160,x,y,u⟩
def p206 (l h x y u:Nat):Rectangle:=⟨l,h,42518,250,10158,x,y,u⟩
def r0:=p1 7339966 7482862 10326 10358 5661
def r1:=p1 7482863 7625758 10325 10356 5660
def r2:=p8 7625759 7768654 54944 55087 45277
def r3:=p1 7768655 7840102 10329 10361 5658
def r4:=p1 7840103 7911550 10328 10359 5658
def r5:=p1 7911551 7982999 10327 10358 5657
def r6:=p2 7983000 8054447 16702 16749 11313
def r7:=p1 8054448 8090171 10329 10360 5656
def r8:=p1 8090172 8125895 10329 10360 5656
def r9:=p1 8125896 8161619 10329 10360 5655
def r10:=p2 8161620 8197343 16704 16751 11311
def r11:=p2 8197344 8233067 16703 16750 11310
def r12:=p4 8233068 8268791 29452 29531 22620
def r13:=p2 8268792 8286653 16704 16752 11309
def r14:=p2 8286654 8304515 16704 16751 11309
def r15:=p2 8304516 8322377 16704 16750 11308
def r16:=p4 8322378 8340239 29454 29534 22617
def r17:=p4 8340240 8358101 29453 29532 22616
def r18:=p8 8358102 8375963 54953 55096 45232
def r19:=p4 8375964 8384894 29454 29535 22615
def r20:=p4 8384895 8393825 29454 29533 22615
def r21:=p4 8393826 8402756 29454 29532 22615
def r22:=p8 8402757 8411687 54953 55099 45229
def r23:=p4 8411688 8416153 29454 29533 22614
def r24:=p4 8416154 8420618 29454 29533 22614
def r25:=p8 8420619 8425084 54954 55102 45228
def r26:=p8 8425085 8429549 54954 55100 45228
def r27:=p8 8429550 8434015 54954 55099 45228
def r28:=p8 8434016 8438480 54953 55097 45227
def r29:=p206 8438481 8442946 2622213 2630842 42951
def r30:=p206 8442947 8447411 2623399 2632052 42943
def r31:=p206 8447412 8451877 2624600 2633275 42934
def r32:=p206 8451878 8456342 2625780 2634477 42926
def r33:=p206 8456343 8460808 2626982 2635700 42917
def r34:=p206 8460809 8465273 2628154 2636894 42909
def r35:=p206 8465274 8469739 2629357 2638117 42900
def r36:=p206 8469740 8474204 2630522 2639302 42892
def r37:=p206 8474205 8478670 2631725 2640525 42883
def r38:=p206 8478671 8483135 2632883 2641703 42875
def r39:=p206 8483136 8492067 2827411 2816343 42866
def r40:=p206 8492068 8500998 2803669 2798588 42849
def r41:=p206 8500999 8509929 2791477 2789783 42832
def r42:=p206 8509930 8518860 2784490 2784976 42815
def r43:=p206 8518861 8527791 2780343 2782353 42798
def r44:=p206 8527792 8536722 2777918 2781053 42781
def r45:=p206 8536723 8545653 2776617 2780616 42764
def r46:=p206 8545654 8554584 2776089 2780775 42747
def r47:=p206 8554585 8563515 2776117 2781363 42730
def r48:=p206 8563516 8572446 2776559 2782269 42713
def r49:=p206 8572447 8581377 2777325 2783427 42696
def r50:=p206 8581378 8590308 2778354 2784792 42679
def r51:=p206 8590309 8599239 2779578 2786308 42662
def r52:=p206 8599240 8608170 2780961 2787946 42645
def r53:=p206 8608171 8617101 2782476 2789685 42628
def r54:=p206 8617102 8626032 2784099 2791510 42611
def r55:=p206 8626033 8634963 2785816 2793407 42594
def r56:=p206 8634964 8643894 2787612 2795366 42577
def r57:=p206 8643895 8652825 2789477 2797379 42560
def r58:=p206 8652826 8661756 2791401 2799439 42543
def r59:=p206 8661757 8670687 2793386 2801548 42526
def r60:=p206 8670688 8679618 2795422 2803699 42509
def r61:=p206 8679619 8688549 2797497 2805879 42492
def r62:=p206 8688550 8697480 2799608 2808089 42474
def r63:=p206 8697481 8706411 2801752 2810325 42457
def r64:=p206 8706412 8715342 2803927 2812586 42440
def r65:=p206 8715343 8724273 2806130 2814869 42423
def r66:=p206 8724274 8733204 2808358 2817173 42406
def r67:=p206 8733205 8742135 2810610 2819497 42389
def r68:=p206 8742136 8751066 2812885 2821839 42372
def r69:=p206 8751067 8759997 2815187 2824205 42355
def r70:=p206 8759998 8768928 2817510 2826589 42338
def r71:=p206 8768929 8777859 2819851 2828988 42321
def r72:=p206 8777860 8786790 2822209 2831401 42304
def r73:=p206 8786791 8795721 2824582 2833827 42287
def r74:=p206 8795722 8804652 2826970 2836266 42270
def r75:=p206 8804653 8813583 2829373 2838717 42253
def r76:=p206 8813584 8822514 2831789 2841180 42236
def r77:=p206 8822515 8831445 2834218 2843654 42219
def r78:=p206 8831446 8840376 2836661 2846140 42202
def r79:=p206 8840377 8849307 2839122 2848643 42185
def r80:=p206 8849308 8858238 2841596 2851157 42168
def r81:=p206 8858239 8867169 2844080 2853680 42151
def r82:=p206 8867170 8876100 2846575 2856213 42134
def r83:=p206 8876101 8885031 2849081 2858755 42117
def r84:=p206 8885032 8893962 2851597 2861306 42100
def r85:=p206 8893963 8902893 2854123 2863866 42083
def r86:=p206 8902894 8911824 2856658 2866435 42066
def r87:=p206 8911825 8920755 2859204 2869013 42049
def r88:=p206 8920756 8929686 2861761 2871602 42032
def r89:=p206 8929687 8938617 2864330 2874202 42015
def r90:=p206 8938618 8947548 2866907 2876810 41998
def r91:=p206 8947549 8956479 2869493 2879425 41980
def r92:=p206 8956480 8965410 2872520 2882048 41963
def r93:=p206 8965411 8974341 2876568 2885968 41946
def r94:=p206 8974342 8983272 2880556 2890014 41929
def r95:=p206 8983273 8992203 2884491 2894004 41912
def r96:=p206 8992204 9001134 2888376 2897941 41895
def r97:=p206 9001135 9010065 2892216 2901832 41878
def r98:=p206 9010066 9018996 2896019 2905684 41861
def r99:=p206 9018997 9027927 2899786 2909499 41844
def r100:=p206 9027928 9036858 2903519 2913277 41827
def r101:=p206 9036859 9045789 2907218 2917020 41810
def r102:=p206 9045790 9054720 2910888 2920732 41793
def r103:=p206 9054721 9063652 2914550 2924436 41776
def r104:=p206 9063653 9072583 2918146 2928072 41759
def r105:=p206 9072584 9081514 2921739 2931704 41742
def r106:=p206 9081515 9090445 2925310 2935313 41725
def r107:=p206 9090446 9099376 2928862 2938902 41708
def r108:=p206 9099377 9108307 2932400 2942477 41691
def r109:=p206 9108308 9117238 2935923 2946034 41674
def r110:=p206 9117239 9126169 2939430 2949575 41657
def r111:=p206 9126170 9144031 3267090 3275104 41640
def r112:=p206 9144032 9161893 3254148 3262655 41606
def r113:=p206 9161894 9179755 3245438 3254337 41572
def r114:=p206 9179756 9197617 3239741 3248960 41538
def r115:=p206 9197618 9215479 3236276 3245764 41504
def r116:=p206 9215480 9233341 3234489 3244206 41469
def r117:=p206 9233342 9251203 3234010 3243925 41435
def r118:=p206 9251204 9269065 3234570 3244659 41401
def r119:=p206 9269066 9286927 3235984 3246229 41367
def r120:=p206 9286928 9304789 3238107 3248491 41333
def r121:=p206 9304790 9322651 3240807 3251318 41299
def r122:=p206 9322652 9340513 3243996 3254623 41265
def r123:=p206 9340514 9358375 3247603 3258337 41231
def r124:=p206 9358376 9376237 3251585 3262418 41197
def r125:=p206 9376238 9394099 3255892 3266817 41163
def r126:=p206 9394100 9411961 3260477 3271488 41129
def r127:=p206 9411962 9429823 3265309 3276402 41095
def r128:=p206 9429824 9447685 3270363 3281533 41061
def r129:=p206 9447686 9465547 3275925 3286868 41027
def r130:=p206 9465548 9483409 3284706 3295222 40992
def r131:=p206 9483410 9501271 3293390 3304057 40958
def r132:=p206 9501272 9519133 3302001 3312804 40924
def r133:=p206 9519134 9536995 3310557 3321486 40890
def r134:=p206 9536996 9554857 3319090 3330135 40856
def r135:=p206 9554858 9572719 3327596 3338751 40822
def r136:=p206 9572720 9590581 3336082 3347339 40788
def r137:=p206 9590582 9608443 3344556 3355909 40754
def r138:=p206 9608444 9626305 3353026 3364470 40720
def r139:=p206 9626306 9644168 3361539 3373070 40686
def r140:=p206 9644169 9662030 3370009 3381623 40652
def r141:=p206 9662031 9679892 3378514 3390207 40618
def r142:=p206 9679893 9697754 3387034 3398803 40584
def r143:=p206 9697755 9715616 3395572 3407414 40550
def r144:=p206 9715617 9733478 3404141 3416054 40516
def r145:=p206 9733479 9751340 3412735 3424716 40481
def r146:=p206 9751341 9769202 3421355 3433403 40447
def r147:=p206 9769203 9787064 3430004 3442116 40413
def r148:=p206 9787065 9804926 3438687 3450862 40379
def r149:=p206 9804927 9822788 3448992 3460816 40345
def r150:=p206 9822789 9840650 3461092 3473013 40311
def r151:=p206 9840651 9858512 3473025 3485039 40277
def r152:=p206 9858513 9876374 3484813 3496916 40243
def r153:=p206 9876375 9894236 3496484 3508673 40209
def r154:=p206 9894237 9912098 3508060 3520332 40175
def r155:=p206 9912099 9929960 3519545 3531897 40141
def r156:=p206 9929961 9947822 3530952 3543382 40107
def r157:=p206 9947823 9965684 3542294 3554799 40073
def r158:=p206 9965685 9983546 3553585 3566164 40039
def r159:=p206 9983547 10001408 3564840 3577490 40004
def r160:=p206 10001409 10019270 3576059 3588779 39970
def r161:=p206 10019271 10037132 3587250 3600039 39936
def r162:=p206 10037133 10054994 3598421 3611277 39902
def r163:=p206 10054995 10090718 4386776 4399073 39868
def r164:=p206 10090719 10126442 4348772 4361701 39800
def r165:=p206 10126443 10162166 4329548 4342951 39732
def r166:=p206 10162167 10197890 4322087 4335869 39664
def r167:=p206 10197891 10233615 4322464 4336562 39596
def r168:=p206 10233616 10269339 4328279 4342649 39527
def r169:=p206 10269340 10305063 4338269 4352881 39459
def r170:=p206 10305064 10340787 4351422 4366254 39391
def r171:=p206 10340788 10376511 4367135 4382170 39323
def r172:=p206 10376512 10412235 4384900 4400126 39255
def r173:=p206 10412236 10447959 4407861 4422486 39187
def r174:=p206 10447960 10483683 4438264 4453206 39119
def r175:=p206 10483684 10519407 4469135 4484362 39051
def r176:=p206 10519408 10555131 4500530 4516020 38982
def r177:=p206 10555132 10590855 4532415 4548149 38914
def r178:=p206 10590856 10626579 4564862 4580826 38846
def r179:=p206 10626580 10662303 4597831 4614015 38778
def r180:=p206 10662304 10698027 4631358 4647753 38710
def r181:=p206 10698028 10733751 4665461 4682060 38642
def r182:=p206 10733752 10769475 4700112 4716910 38574
def r183:=p206 10769476 10805200 4735419 4752412 38505
def r184:=p206 10805201 10840924 4779738 4796561 38437
def r185:=p206 10840925 10876648 4826914 4844001 38369
def r186:=p206 10876649 10912372 4873975 4891316 38301
def r187:=p206 10912373 10948096 4921057 4938645 38233
def r188:=p206 10948097 10983820 4968320 4986149 38165
def r189:=p206 10983821 11019544 5015810 5033876 38097
def r190:=p206 11019545 11055268 5063666 5081966 38028
def r191:=p206 11055269 11090992 5111950 5130480 37960
def r192:=p206 11090993 11126716 5160736 5179496 37892
def r193:=p206 11126717 11162440 5222731 5241475 37824
def r194:=p206 11162441 11198164 5284710 5303747 37756
def r195:=p206 11198165 11233888 5346797 5366123 37688
def r196:=p206 11233889 11269612 5409092 5428703 37620
def r197:=p206 11269613 11341060 9310086 9335995 37551
def r198:=p206 11341061 11412509 8891828 8919274 37415
def r199:=p206 11412510 11483957 8789185 8817821 37279
def r200:=p206 11483958 11555405 8822871 8852590 37143
def r201:=p206 11555406 11626853 8932496 8963272 37006
def r202:=p206 11626854 11698301 9093048 9124894 36870
def r203:=p206 11698302 11769749 9292752 9325703 36734
def r204:=p206 11769750 11841197 9525808 9559915 36598
def r205:=p206 11841198 11912645 9804534 9839106 36461

def b0 : List (Rectangle × FastWitness) := [(r0,⟨66,42,44⟩),(r1,⟨66,41,42⟩),(r2,⟨66,43,45⟩),(r3,⟨66,45,47⟩),(r4,⟨66,44,45⟩),(r5,⟨66,43,44⟩),(r6,⟨66,44,46⟩),(r7,⟨66,45,46⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨66,45,46⟩),(r9,⟨66,45,46⟩),(r10,⟨66,46,47⟩),(r11,⟨66,45,47⟩),(r12,⟨66,45,47⟩),(r13,⟨66,46,48⟩),(r14,⟨66,46,47⟩),(r15,⟨66,46,47⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨66,46,49⟩),(r17,⟨66,46,48⟩),(r18,⟨66,46,49⟩),(r19,⟨66,46,50⟩),(r20,⟨66,46,48⟩),(r21,⟨66,46,48⟩),(r22,⟨66,46,50⟩),(r23,⟨66,46,48⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨66,46,48⟩),(r25,⟨66,47,51⟩),(r26,⟨66,47,51⟩),(r27,⟨66,47,50⟩),(r28,⟨66,46,49⟩),(r29,⟨66,45,45⟩),(r30,⟨66,45,45⟩),(r31,⟨66,45,45⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨66,45,45⟩),(r33,⟨66,45,45⟩),(r34,⟨66,45,45⟩),(r35,⟨66,45,45⟩),(r36,⟨66,45,45⟩),(r37,⟨66,45,45⟩),(r38,⟨66,45,45⟩),(r39,⟨66,47,47⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨66,47,47⟩),(r41,⟨66,47,47⟩),(r42,⟨66,47,47⟩),(r43,⟨66,47,47⟩),(r44,⟨66,47,47⟩),(r45,⟨66,47,47⟩),(r46,⟨66,47,47⟩),(r47,⟨66,47,47⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨66,47,47⟩),(r49,⟨66,47,47⟩),(r50,⟨66,47,47⟩),(r51,⟨66,47,47⟩),(r52,⟨66,47,47⟩),(r53,⟨66,47,47⟩),(r54,⟨66,47,47⟩),(r55,⟨66,47,47⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨66,47,47⟩),(r57,⟨66,47,47⟩),(r58,⟨66,47,47⟩),(r59,⟨66,47,47⟩),(r60,⟨66,47,47⟩),(r61,⟨66,47,47⟩),(r62,⟨66,47,47⟩),(r63,⟨66,47,47⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨66,47,47⟩),(r65,⟨66,47,47⟩),(r66,⟨66,47,47⟩),(r67,⟨66,47,47⟩),(r68,⟨66,47,47⟩),(r69,⟨66,47,47⟩),(r70,⟨66,47,47⟩),(r71,⟨66,47,47⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨66,47,47⟩),(r73,⟨66,47,47⟩),(r74,⟨66,47,47⟩),(r75,⟨66,47,47⟩),(r76,⟨66,47,47⟩),(r77,⟨66,47,47⟩),(r78,⟨66,47,47⟩),(r79,⟨66,47,47⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨66,47,47⟩),(r81,⟨66,47,47⟩),(r82,⟨66,47,47⟩),(r83,⟨66,47,47⟩),(r84,⟨66,47,47⟩),(r85,⟨66,47,47⟩),(r86,⟨66,47,47⟩),(r87,⟨66,47,47⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨66,47,47⟩),(r89,⟨66,47,47⟩),(r90,⟨66,47,47⟩),(r91,⟨66,47,47⟩),(r92,⟨66,47,48⟩),(r93,⟨66,48,48⟩),(r94,⟨66,48,48⟩),(r95,⟨66,48,48⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨66,48,48⟩),(r97,⟨66,48,48⟩),(r98,⟨66,48,48⟩),(r99,⟨66,48,48⟩),(r100,⟨66,48,48⟩),(r101,⟨66,48,48⟩),(r102,⟨66,48,48⟩),(r103,⟨66,48,48⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨66,48,48⟩),(r105,⟨66,48,48⟩),(r106,⟨66,48,48⟩),(r107,⟨66,48,48⟩),(r108,⟨66,48,48⟩),(r109,⟨66,48,48⟩),(r110,⟨66,48,48⟩),(r111,⟨66,50,50⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨66,50,50⟩),(r113,⟨66,50,50⟩),(r114,⟨66,50,50⟩),(r115,⟨66,50,50⟩),(r116,⟨66,50,50⟩),(r117,⟨66,50,50⟩),(r118,⟨66,50,50⟩),(r119,⟨66,50,50⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨66,50,50⟩),(r121,⟨66,50,50⟩),(r122,⟨66,50,50⟩),(r123,⟨66,50,50⟩),(r124,⟨66,50,50⟩),(r125,⟨66,50,50⟩),(r126,⟨66,50,50⟩),(r127,⟨66,50,50⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨66,50,50⟩),(r129,⟨66,50,51⟩),(r130,⟨66,51,51⟩),(r131,⟨66,51,51⟩),(r132,⟨66,51,51⟩),(r133,⟨66,51,51⟩),(r134,⟨66,51,51⟩),(r135,⟨66,51,51⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨66,51,51⟩),(r137,⟨66,51,51⟩),(r138,⟨66,51,51⟩),(r139,⟨66,51,51⟩),(r140,⟨66,51,51⟩),(r141,⟨66,51,51⟩),(r142,⟨66,51,51⟩),(r143,⟨66,51,51⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨66,51,51⟩),(r145,⟨66,51,51⟩),(r146,⟨66,51,51⟩),(r147,⟨66,51,51⟩),(r148,⟨66,51,51⟩),(r149,⟨66,52,52⟩),(r150,⟨66,52,52⟩),(r151,⟨66,52,52⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨66,52,52⟩),(r153,⟨66,52,52⟩),(r154,⟨66,52,52⟩),(r155,⟨66,52,52⟩),(r156,⟨66,52,52⟩),(r157,⟨66,52,52⟩),(r158,⟨66,52,52⟩),(r159,⟨66,52,52⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨66,52,52⟩),(r161,⟨66,52,52⟩),(r162,⟨66,52,52⟩),(r163,⟨66,55,55⟩),(r164,⟨66,55,55⟩),(r165,⟨66,55,55⟩),(r166,⟨66,55,55⟩),(r167,⟨66,55,55⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨66,55,55⟩),(r169,⟨66,55,55⟩),(r170,⟨66,55,55⟩),(r171,⟨66,55,55⟩),(r172,⟨66,55,55⟩),(r173,⟨66,56,56⟩),(r174,⟨66,56,56⟩),(r175,⟨66,56,56⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨66,56,56⟩),(r177,⟨66,56,56⟩),(r178,⟨66,56,56⟩),(r179,⟨66,56,56⟩),(r180,⟨66,56,56⟩),(r181,⟨66,56,56⟩),(r182,⟨66,56,56⟩),(r183,⟨66,56,56⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨66,57,57⟩),(r185,⟨66,57,57⟩),(r186,⟨66,57,57⟩),(r187,⟨66,57,57⟩),(r188,⟨66,57,57⟩),(r189,⟨66,57,57⟩),(r190,⟨66,57,57⟩),(r191,⟨66,57,57⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨66,57,57⟩),(r193,⟨66,58,58⟩),(r194,⟨66,58,58⟩),(r195,⟨66,58,58⟩),(r196,⟨66,58,58⟩),(r197,⟨66,62,62⟩),(r198,⟨66,62,62⟩),(r199,⟨66,62,62⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨66,62,62⟩),(r201,⟨66,62,62⟩),(r202,⟨66,62,62⟩),(r203,⟨66,62,62⟩),(r204,⟨66,62,62⟩),(r205,⟨66,63,63⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25
def rows : List Rectangle := witnessedRows.map Prod.fst
theorem all_fast_checked : fastCheckList band witnessedRows=true := by
  have joinChecked (xs ys : List (Rectangle × FastWitness)) (hx : fastCheckList band xs = true) (hy : fastCheckList band ys = true) : fastCheckList band (xs ++ ys) = true := by
    rw [fastCheckList_append, hx, hy]
    rfl
  exact (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24) b25 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23) b24 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22) b23 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21) b22 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20) b21 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19) b20 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18) b19 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17) b18 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16) b17 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15) b16 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14) b15 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13) b14 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12) b13 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11) b12 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10) b11 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8++b9) b10 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7++b8) b9 (joinChecked (b0++b1++b2++b3++b4++b5++b6++b7) b8 (joinChecked (b0++b1++b2++b3++b4++b5++b6) b7 (joinChecked (b0++b1++b2++b3++b4++b5) b6 (joinChecked (b0++b1++b2++b3++b4) b5 (joinChecked (b0++b1++b2++b3) b4 (joinChecked (b0++b1++b2) b3 (joinChecked (b0++b1) b2 (joinChecked (b0) b1 checked0 checked1) checked2) checked3) checked4) checked5) checked6) checked7) checked8) checked9) checked10) checked11) checked12) checked13) checked14) checked15) checked16) checked17) checked18) checked19) checked20) checked21) checked22) checked23) checked24) checked25)
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR10B56T3902To3917Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 10)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 10≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤56)
    (hT0 : 3902≤T) (hT1 : T≤3917) (hnu : 7339966≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤12314372801839158 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR10B56T3902To3917Fast


