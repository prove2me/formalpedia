-- Prove2me | Definitions.Def_Yukon_b9898b64429801647a447267
-- name    : Yukon_b9898b64429801647a447267
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-02T20:14:44.984685+00:00
-- url     : https://prove2.me/theorems/4ea87b9c-d80d-416f-8044-35759b36381b
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.RelativeCertR12B49T3885To3924Fast.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR12B49T3885To3924Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B49T3885To3924Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR12B49T3885To3924Fast.lean
--
--   yukon-proof-operation:certificate-split-0b37e588fc1b5f6c31d0659336f4474095fce84d480576ba9d366f9cf61e375e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYzVkYjQ0ZTQyY2RhNGViMTdjY2JlMTFhZDRhMDJkNmEzYTBmYjM2ZTM1YWMwNzBiODk3NmJlZWRkYTgwNmQ4ZCIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXNwbGl0LTBiMzdlNTg4ZmMxYjVmNmMzMWQwNjU5MzM2ZjQ0NzQwOTVmY2U4NGQ0ODA1NzZiYTlkMzY2ZjljZjYxZTM3NWUiLCJ0YWciOiJiZXR0ZXItY29kZXMiLCJ0YXJnZXQiOiJZdWtvbl9iOTg5OGI2NDQyOTgwMTY0N2E0NDcyNjciLCJ2IjoyfQ]

import Definitions.Def_Yukon_e757298719adf05c20287f89

import Definitions.Def_Yukon_7ae729a7570072f2e3e200d8











































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: f1eb2c9d283f2dcc845cee73ca635f965ac927d36b622f8bbd622b785bf24878.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR12B49T3885To3924Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def band : Band := ⟨12,49,3885,3924,11380060537880462⟩

def p1 (l h x y u:Nat):Rectangle:=⟨l,h,4134,1,1270,x,y,u⟩
def p2 (l h x y u:Nat):Rectangle:=⟨l,h,8268,2,2540,x,y,u⟩
def p4 (l h x y u:Nat):Rectangle:=⟨l,h,16536,4,5080,x,y,u⟩
def p8 (l h x y u:Nat):Rectangle:=⟨l,h,33072,8,10160,x,y,u⟩
def p206 (l h x y u:Nat):Rectangle:=⟨l,h,41268,250,10158,x,y,u⟩
def r0:=p1 6422467 6708960 10295 10376 5668
def r1:=p1 6708961 6852207 10313 10383 5666
def r2:=p1 6852208 6995454 10311 10393 5665
def r3:=p1 6995455 7138701 10308 10391 5664
def r4:=p1 7138702 7281948 10304 10387 5663
def r5:=p1 7281949 7425195 10299 10382 5662
def r6:=p2 7425196 7568442 16660 16784 11322
def r7:=p1 7568443 7640066 10307 10392 5660
def r8:=p1 7640067 7711689 10304 10388 5659
def r9:=p1 7711690 7783313 10301 10385 5658
def r10:=p2 7783314 7854936 16665 16795 11316
def r11:=p4 7854937 7926560 29387 29608 22631
def r12:=p1 7926561 7962372 10303 10387 5657
def r13:=p1 7962373 7998183 10303 10385 5657
def r14:=p2 7998184 8033995 16666 16798 11313
def r15:=p2 8033996 8069807 16664 16793 11313
def r16:=p4 8069808 8105619 29388 29612 22625
def r17:=p8 8105620 8141430 54834 55175 45247
def r18:=p2 8141431 8159336 16665 16795 11311
def r19:=p2 8159337 8177242 16664 16792 11311
def r20:=p4 8177243 8195148 29389 29613 22621
def r21:=p4 8195149 8213054 29388 29608 22621
def r22:=p8 8213055 8230960 54835 55179 45241
def r23:=p4 8230961 8239913 29389 29614 22620
def r24:=p4 8239914 8248866 29388 29611 22619
def r25:=p8 8248867 8257819 54837 55169 45239
def r26:=p8 8257820 8266772 54836 55175 45238
def r27:=p4 8266773 8271249 29388 29611 22618
def r28:=p4 8271250 8275725 29388 29610 22618
def r29:=p8 8275726 8280201 54837 55170 45237
def r30:=p8 8280202 8284677 54836 55173 45237
def r31:=p8 8284678 8289154 54836 55176 45236
def r32:=p8 8289155 8293630 54836 55179 45236
def r33:=p206 8293631 8298107 3061398 3084893 41499
def r34:=p206 8298108 8302583 3063116 3086789 41491
def r35:=p206 8302584 8307060 3064960 3088804 41482
def r36:=p206 8307061 8311536 3066646 3090654 41474
def r37:=p206 8311537 8316013 3068479 3092645 41465
def r38:=p206 8316014 8320489 3070157 3094474 41456
def r39:=p206 8320490 8324966 3071970 3096434 41448
def r40:=p206 8324967 8329442 3073655 3098261 41439
def r41:=p206 8329443 8333919 3075437 3100180 41431
def r42:=p206 8333920 8338395 3077131 3102005 41422
def r43:=p206 8338396 8342872 3078885 3103887 41414
def r44:=p206 8342873 8347348 3080587 3105712 41405
def r45:=p206 8347349 8351825 3082326 3107571 41397
def r46:=p206 8351826 8356301 3084027 3109388 41388
def r47:=p206 8356302 8360778 3085763 3111236 41380
def r48:=p206 8360779 8365254 3087453 3113035 41371
def r49:=p206 8365255 8369731 3089187 3114876 41363
def r50:=p206 8369732 8374207 3090859 3116650 41354
def r51:=p206 8374208 8378684 3092601 3118492 41345
def r52:=p206 8378685 8383160 3094264 3120253 41337
def r53:=p206 8383161 8387637 3096005 3122089 41328
def r54:=p206 8387638 8392113 3097670 3123846 41320
def r55:=p206 8392114 8396590 3099402 3125669 41311
def r56:=p206 8396591 8401066 3101069 3127423 41303
def r57:=p206 8401067 8405543 3102793 3129233 41294
def r58:=p206 8405544 8410019 3104462 3130986 41286
def r59:=p206 8410020 8414496 3106188 3132795 41277
def r60:=p206 8414497 8418972 3107851 3134537 41269
def r61:=p206 8418973 8423448 3109555 3136319 41260
def r62:=p206 8423449 8427924 3111236 3138077 41252
def r63:=p206 8427925 8432401 3112974 3139890 41243
def r64:=p206 8432402 8436877 3114618 3141608 41234
def r65:=p206 8436878 8441354 3116358 3143420 41226
def r66:=p206 8441355 8445830 3118009 3145141 41217
def r67:=p206 8445831 8450307 3119741 3146943 41209
def r68:=p206 8450308 8454783 3121404 3148673 41200
def r69:=p206 8454784 8459260 3123124 3150460 41192
def r70:=p206 8459261 8463736 3124798 3152199 41183
def r71:=p206 8463737 8468213 3126507 3153972 41175
def r72:=p206 8468214 8472689 3128193 3155720 41166
def r73:=p206 8472690 8477166 3129900 3157489 41158
def r74:=p206 8477167 8481642 3131587 3159238 41149
def r75:=p206 8481643 8486119 3133298 3161008 41141
def r76:=p206 8486120 8490595 3134978 3162747 41132
def r77:=p206 8490596 8495072 3136698 3164525 41123
def r78:=p206 8495073 8499548 3138369 3166252 41115
def r79:=p206 8499549 8504025 3140100 3168040 41106
def r80:=p206 8504026 8508501 3141771 3169766 41098
def r81:=p206 8508502 8512978 3143503 3171553 41089
def r82:=p206 8512979 8517454 3145180 3173283 41081
def r83:=p206 8517455 8521931 3146910 3175066 41072
def r84:=p206 8521932 8526407 3148591 3176799 41064
def r85:=p206 8526408 8535360 3464179 3476434 41055
def r86:=p206 8535361 8544313 3448498 3463207 41038
def r87:=p206 8544314 8553266 3436874 3453532 41021
def r88:=p206 8553267 8562219 3428159 3446403 41004
def r89:=p206 8562220 8571171 3421521 3441084 40987
def r90:=p206 8571172 8580124 3416768 3437447 40970
def r91:=p206 8580125 8589077 3413179 3434814 40953
def r92:=p206 8589078 8598030 3410604 3433069 40936
def r93:=p206 8598031 8606983 3408833 3432027 40919
def r94:=p206 8606984 8615936 3407733 3431573 40901
def r95:=p206 8615937 8624889 3407197 3431612 40884
def r96:=p206 8624890 8633842 3407158 3432091 40867
def r97:=p206 8633843 8642795 3407531 3432935 40850
def r98:=p206 8642796 8651748 3408248 3434079 40833
def r99:=p206 8651749 8660701 3409261 3435484 40816
def r100:=p206 8660702 8669654 3410532 3437116 40799
def r101:=p206 8669655 8678607 3412030 3438947 40782
def r102:=p206 8678608 8687560 3413729 3440955 40765
def r103:=p206 8687561 8696513 3415626 3443141 40748
def r104:=p206 8696514 8705466 3417688 3445473 40731
def r105:=p206 8705467 8714418 3419844 3447881 40714
def r106:=p206 8714419 8723371 3422214 3450490 40697
def r107:=p206 8723372 8732324 3424649 3453150 40679
def r108:=p206 8732325 8741277 3427191 3455905 40662
def r109:=p206 8741278 8750230 3429831 3458747 40645
def r110:=p206 8750231 8759183 3432577 3461686 40628
def r111:=p206 8759184 8768136 3435410 3464701 40611
def r112:=p206 8768137 8777089 3438317 3467784 40594
def r113:=p206 8777090 8786042 3441295 3470929 40577
def r114:=p206 8786043 8794995 3444338 3474133 40560
def r115:=p206 8794996 8803948 3447441 3477391 40543
def r116:=p206 8803949 8812901 3450603 3480702 40526
def r117:=p206 8812902 8821854 3453834 3484076 40509
def r118:=p206 8821855 8830807 3457117 3487497 40492
def r119:=p206 8830808 8839760 3460441 3490955 40475
def r120:=p206 8839761 8848713 3463806 3494451 40457
def r121:=p206 8848714 8857665 3467520 3497953 40440
def r122:=p206 8857666 8866618 3473822 3501556 40423
def r123:=p206 8866619 8875571 3479935 3507920 40406
def r124:=p206 8875572 8884524 3485952 3514247 40389
def r125:=p206 8884525 8893477 3491864 3520450 40372
def r126:=p206 8893478 8902430 3497681 3526541 40355
def r127:=p206 8902431 8911383 3503415 3532534 40338
def r128:=p206 8911384 8920336 3509074 3538438 40321
def r129:=p206 8920337 8929289 3514667 3544264 40304
def r130:=p206 8929290 8938242 3520204 3550023 40287
def r131:=p206 8938243 8947195 3525707 3555738 40270
def r132:=p206 8947196 8956148 3531155 3561389 40253
def r133:=p206 8956149 8965101 3536557 3566984 40235
def r134:=p206 8965102 8974054 3541920 3572533 40218
def r135:=p206 8974055 8983007 3547250 3578041 40201
def r136:=p206 8983008 8991960 3552549 3583513 40184
def r137:=p206 8991961 9000912 3557789 3588919 40167
def r138:=p206 9000913 9009865 3563093 3594383 40150
def r139:=p206 9009866 9018818 3568339 3599784 40133
def r140:=p206 9018819 9027771 3573565 3605161 40116
def r141:=p206 9027772 9036724 3578775 3610516 40099
def r142:=p206 9036725 9045677 3583969 3615852 40082
def r143:=p206 9045678 9054630 3589151 3621170 40065
def r144:=p206 9054631 9063583 3594326 3626480 40048
def r145:=p206 9063584 9072536 3599499 3631783 40031
def r146:=p206 9072537 9081489 3604659 3637070 40013
def r147:=p206 9081490 9090442 3609812 3642347 39996
def r148:=p206 9090443 9099395 3614960 3647615 39979
def r149:=p206 9099396 9108348 3620103 3652877 39962
def r150:=p206 9108349 9117301 3625243 3658132 39945
def r151:=p206 9117302 9126254 3630386 3663390 39928
def r152:=p206 9126255 9135207 3635537 3668652 39911
def r153:=p206 9135208 9144159 3640660 3673884 39894
def r154:=p206 9144160 9153112 3645837 3679168 39877
def r155:=p206 9153113 9162065 3650988 3684425 39860
def r156:=p206 9162066 9171018 3656141 3689681 39843
def r157:=p206 9171019 9179971 3663665 3695700 39826
def r158:=p206 9179972 9188924 3671351 3703572 39809
def r159:=p206 9188925 9197877 3678938 3711339 39792
def r160:=p206 9197878 9206830 3686430 3719005 39774
def r161:=p206 9206831 9215783 3693834 3726578 39757
def r162:=p206 9215784 9233689 4374897 4379335 39740
def r163:=p206 9233690 9251595 4296271 4310518 39706
def r164:=p206 9251596 9269501 4256437 4276378 39672
def r165:=p206 9269502 9287406 4234704 4258385 39638
def r166:=p206 9287407 9305312 4223436 4249782 39604
def r167:=p206 9305313 9323218 4218250 4246602 39570
def r168:=p206 9323219 9341124 4217223 4247149 39535
def r169:=p206 9341125 9359030 4219053 4250255 39501
def r170:=p206 9359031 9376936 4222981 4255247 39467
def r171:=p206 9376937 9394842 4228560 4261730 39433
def r172:=p206 9394843 9412748 4235349 4269302 39399
def r173:=p206 9412749 9430653 4243003 4277644 39365
def r174:=p206 9430654 9448559 4251635 4286891 39330
def r175:=p206 9448560 9466465 4260872 4296681 39296
def r176:=p206 9466466 9484371 4270663 4306976 39262
def r177:=p206 9484372 9502277 4280947 4317723 39228
def r178:=p206 9502278 9520183 4291693 4328898 39194
def r179:=p206 9520184 9538089 4302799 4340404 39160
def r180:=p206 9538090 9555995 4314207 4352188 39126
def r181:=p206 9555996 9573900 4325908 4364243 39091
def r182:=p206 9573901 9591806 4337987 4376660 39057
def r183:=p206 9591807 9609712 4350269 4389262 39023
def r184:=p206 9609713 9627618 4362800 4402101 38989
def r185:=p206 9627619 9645524 4375580 4415177 38955
def r186:=p206 9645525 9663430 4388552 4428435 38921
def r187:=p206 9663431 9681336 4401710 4441869 38886
def r188:=p206 9681337 9699242 4415458 4455523 38852
def r189:=p206 9699243 9717147 4435897 4474650 38818
def r190:=p206 9717148 9735053 4456114 4495331 38784
def r191:=p206 9735054 9752959 4476030 4515684 38750
def r192:=p206 9752960 9770865 4495755 4535824 38716
def r193:=p206 9770866 9788771 4515277 4555741 38682
def r194:=p206 9788772 9806677 4534660 4575502 38647
def r195:=p206 9806678 9824583 4553985 4595191 38613
def r196:=p206 9824584 9842489 4573231 4614787 38579
def r197:=p206 9842490 9860394 4592377 4634271 38545
def r198:=p206 9860395 9878300 4611598 4653821 38511
def r199:=p206 9878301 9896206 4630768 4673311 38477
def r200:=p206 9896207 9914112 4649924 4692779 38442
def r201:=p206 9914113 9932018 4669099 4712258 38408
def r202:=p206 9932019 9949924 4688339 4731796 38374
def r203:=p206 9949925 9967830 4707618 4751368 38340
def r204:=p206 9967831 9985736 4726945 4770982 38306
def r205:=p206 9985737 10003641 4746319 4790639 38272
def r206:=p206 10003642 10021547 4768823 4812153 38238
def r207:=p206 10021548 10039453 4795464 4839208 38203
def r208:=p206 10039454 10057359 4821821 4865968 38169
def r209:=p206 10057360 10075265 4847976 4892514 38135
def r210:=p206 10075266 10093171 4873925 4918845 38101
def r211:=p206 10093172 10111077 4899707 4944999 38067
def r212:=p206 10111078 10146888 7078366 7101888 38033
def r213:=p206 10146889 10182700 6699403 6736755 37964
def r214:=p206 10182701 10218512 6559811 6603788 37896
def r215:=p206 10218513 10254324 6506474 6554504 37828
def r216:=p206 10254325 10290135 6494535 6545415 37759
def r217:=p206 10290136 10325947 6506511 6559589 37691
def r218:=p206 10325948 10361759 6533213 6588096 37623
def r219:=p206 10361760 10397571 6570181 6626615 37554
def r220:=p206 10397572 10433382 6614627 6672444 37486
def r221:=p206 10433383 10469194 6665466 6724554 37418
def r222:=p206 10469195 10505006 6720937 6781212 37350
def r223:=p206 10505007 10540818 6780700 6842105 37281
def r224:=p206 10540819 10576629 6844134 6906627 37213
def r225:=p206 10576630 10612441 6911107 6974663 37145
def r226:=p206 10612442 10648253 6981223 7045822 37076
def r227:=p206 10648254 10684065 7054355 7119987 37008
def r228:=p206 10684066 10719876 7143467 7208168 36940
def r229:=p206 10719877 10755688 7251052 7317273 36871
def r230:=p206 10755689 10791500 7359559 7427253 36803
def r231:=p206 10791501 10827312 7469506 7538638 36735
def r232:=p206 10827313 10863123 7580996 7651545 36667
def r233:=p206 10863124 10898935 7694878 7766832 36598
def r234:=p206 10898936 10934747 7811001 7884357 36530
def r235:=p206 10934748 10970559 7929751 8004511 36462
def r236:=p206 10970560 11006370 8051292 8127464 36393

def b0 : List (Rectangle × FastWitness) := [(r0,⟨61,36,38⟩),(r1,⟨61,45,55⟩),(r2,⟨61,52,55⟩),(r3,⟨61,49,53⟩),(r4,⟨61,45,50⟩),(r5,⟨61,40,45⟩),(r6,⟨61,41,46⟩),(r7,⟨61,48,54⟩)]
theorem checked0 : fastCheckList band b0=true := by decide +kernel

def b1 : List (Rectangle × FastWitness) := [(r8,⟨61,45,51⟩),(r9,⟨61,42,48⟩),(r10,⟨61,45,55⟩),(r11,⟨61,45,58⟩),(r12,⟨61,44,50⟩),(r13,⟨61,44,48⟩),(r14,⟨61,46,57⟩),(r15,⟨61,44,53⟩)]
theorem checked1 : fastCheckList band b1=true := by decide +kernel

def b2 : List (Rectangle × FastWitness) := [(r16,⟨61,45,61⟩),(r17,⟨61,38,45⟩),(r18,⟨61,45,55⟩),(r19,⟨61,44,52⟩),(r20,⟨61,46,61⟩),(r21,⟨61,45,58⟩),(r22,⟨61,39,46⟩),(r23,⟨61,46,61⟩)]
theorem checked2 : fastCheckList band b2=true := by decide +kernel

def b3 : List (Rectangle × FastWitness) := [(r24,⟨61,45,60⟩),(r25,⟨61,35,47⟩),(r26,⟨61,38,46⟩),(r27,⟨61,45,60⟩),(r28,⟨61,45,60⟩),(r29,⟨61,36,47⟩),(r30,⟨61,37,46⟩),(r31,⟨61,38,46⟩)]
theorem checked3 : fastCheckList band b3=true := by decide +kernel

def b4 : List (Rectangle × FastWitness) := [(r32,⟨61,39,46⟩),(r33,⟨61,45,45⟩),(r34,⟨61,45,45⟩),(r35,⟨61,45,45⟩),(r36,⟨61,45,45⟩),(r37,⟨61,45,45⟩),(r38,⟨61,45,45⟩),(r39,⟨61,45,45⟩)]
theorem checked4 : fastCheckList band b4=true := by decide +kernel

def b5 : List (Rectangle × FastWitness) := [(r40,⟨61,45,45⟩),(r41,⟨61,45,45⟩),(r42,⟨61,45,45⟩),(r43,⟨61,45,45⟩),(r44,⟨61,45,45⟩),(r45,⟨61,45,45⟩),(r46,⟨61,45,45⟩),(r47,⟨61,45,45⟩)]
theorem checked5 : fastCheckList band b5=true := by decide +kernel

def b6 : List (Rectangle × FastWitness) := [(r48,⟨61,45,45⟩),(r49,⟨61,45,45⟩),(r50,⟨61,45,45⟩),(r51,⟨61,45,45⟩),(r52,⟨61,45,45⟩),(r53,⟨61,45,45⟩),(r54,⟨61,45,45⟩),(r55,⟨61,45,45⟩)]
theorem checked6 : fastCheckList band b6=true := by decide +kernel

def b7 : List (Rectangle × FastWitness) := [(r56,⟨61,45,45⟩),(r57,⟨61,45,45⟩),(r58,⟨61,45,45⟩),(r59,⟨61,45,45⟩),(r60,⟨61,45,45⟩),(r61,⟨61,45,45⟩),(r62,⟨61,45,45⟩),(r63,⟨61,45,45⟩)]
theorem checked7 : fastCheckList band b7=true := by decide +kernel

def b8 : List (Rectangle × FastWitness) := [(r64,⟨61,45,45⟩),(r65,⟨61,45,45⟩),(r66,⟨61,45,45⟩),(r67,⟨61,45,45⟩),(r68,⟨61,45,45⟩),(r69,⟨61,45,45⟩),(r70,⟨61,45,45⟩),(r71,⟨61,45,45⟩)]
theorem checked8 : fastCheckList band b8=true := by decide +kernel

def b9 : List (Rectangle × FastWitness) := [(r72,⟨61,45,45⟩),(r73,⟨61,45,45⟩),(r74,⟨61,45,45⟩),(r75,⟨61,45,45⟩),(r76,⟨61,45,45⟩),(r77,⟨61,45,45⟩),(r78,⟨61,45,45⟩),(r79,⟨61,45,45⟩)]
theorem checked9 : fastCheckList band b9=true := by decide +kernel

def b10 : List (Rectangle × FastWitness) := [(r80,⟨61,45,45⟩),(r81,⟨61,45,45⟩),(r82,⟨61,45,45⟩),(r83,⟨61,45,45⟩),(r84,⟨61,45,45⟩),(r85,⟨61,47,47⟩),(r86,⟨61,47,47⟩),(r87,⟨61,47,47⟩)]
theorem checked10 : fastCheckList band b10=true := by decide +kernel

def b11 : List (Rectangle × FastWitness) := [(r88,⟨61,47,47⟩),(r89,⟨61,47,47⟩),(r90,⟨61,47,47⟩),(r91,⟨61,47,47⟩),(r92,⟨61,47,47⟩),(r93,⟨61,47,47⟩),(r94,⟨61,47,47⟩),(r95,⟨61,47,47⟩)]
theorem checked11 : fastCheckList band b11=true := by decide +kernel

def b12 : List (Rectangle × FastWitness) := [(r96,⟨61,47,47⟩),(r97,⟨61,47,47⟩),(r98,⟨61,47,47⟩),(r99,⟨61,47,47⟩),(r100,⟨61,47,47⟩),(r101,⟨61,47,47⟩),(r102,⟨61,47,47⟩),(r103,⟨61,47,47⟩)]
theorem checked12 : fastCheckList band b12=true := by decide +kernel

def b13 : List (Rectangle × FastWitness) := [(r104,⟨61,47,47⟩),(r105,⟨61,47,47⟩),(r106,⟨61,47,47⟩),(r107,⟨61,47,47⟩),(r108,⟨61,47,47⟩),(r109,⟨61,47,47⟩),(r110,⟨61,47,47⟩),(r111,⟨61,47,47⟩)]
theorem checked13 : fastCheckList band b13=true := by decide +kernel

def b14 : List (Rectangle × FastWitness) := [(r112,⟨61,47,47⟩),(r113,⟨61,47,47⟩),(r114,⟨61,47,47⟩),(r115,⟨61,47,47⟩),(r116,⟨61,47,47⟩),(r117,⟨61,47,47⟩),(r118,⟨61,47,47⟩),(r119,⟨61,47,47⟩)]
theorem checked14 : fastCheckList band b14=true := by decide +kernel

def b15 : List (Rectangle × FastWitness) := [(r120,⟨61,47,47⟩),(r121,⟨61,47,48⟩),(r122,⟨61,48,48⟩),(r123,⟨61,48,48⟩),(r124,⟨61,48,48⟩),(r125,⟨61,48,48⟩),(r126,⟨61,48,48⟩),(r127,⟨61,48,48⟩)]
theorem checked15 : fastCheckList band b15=true := by decide +kernel

def b16 : List (Rectangle × FastWitness) := [(r128,⟨61,48,48⟩),(r129,⟨61,48,48⟩),(r130,⟨61,48,48⟩),(r131,⟨61,48,48⟩),(r132,⟨61,48,48⟩),(r133,⟨61,48,48⟩),(r134,⟨61,48,48⟩),(r135,⟨61,48,48⟩)]
theorem checked16 : fastCheckList band b16=true := by decide +kernel

def b17 : List (Rectangle × FastWitness) := [(r136,⟨61,48,48⟩),(r137,⟨61,48,48⟩),(r138,⟨61,48,48⟩),(r139,⟨61,48,48⟩),(r140,⟨61,48,48⟩),(r141,⟨61,48,48⟩),(r142,⟨61,48,48⟩),(r143,⟨61,48,48⟩)]
theorem checked17 : fastCheckList band b17=true := by decide +kernel

def b18 : List (Rectangle × FastWitness) := [(r144,⟨61,48,48⟩),(r145,⟨61,48,48⟩),(r146,⟨61,48,48⟩),(r147,⟨61,48,48⟩),(r148,⟨61,48,48⟩),(r149,⟨61,48,48⟩),(r150,⟨61,48,48⟩),(r151,⟨61,48,48⟩)]
theorem checked18 : fastCheckList band b18=true := by decide +kernel

def b19 : List (Rectangle × FastWitness) := [(r152,⟨61,48,48⟩),(r153,⟨61,48,48⟩),(r154,⟨61,48,48⟩),(r155,⟨61,48,48⟩),(r156,⟨61,48,48⟩),(r157,⟨61,49,49⟩),(r158,⟨61,49,49⟩),(r159,⟨61,49,49⟩)]
theorem checked19 : fastCheckList band b19=true := by decide +kernel

def b20 : List (Rectangle × FastWitness) := [(r160,⟨61,49,49⟩),(r161,⟨61,49,49⟩),(r162,⟨61,51,51⟩),(r163,⟨61,51,51⟩),(r164,⟨61,51,51⟩),(r165,⟨61,51,51⟩),(r166,⟨61,51,51⟩),(r167,⟨61,51,51⟩)]
theorem checked20 : fastCheckList band b20=true := by decide +kernel

def b21 : List (Rectangle × FastWitness) := [(r168,⟨61,51,51⟩),(r169,⟨61,51,51⟩),(r170,⟨61,51,51⟩),(r171,⟨61,51,51⟩),(r172,⟨61,51,51⟩),(r173,⟨61,51,51⟩),(r174,⟨61,51,51⟩),(r175,⟨61,51,51⟩)]
theorem checked21 : fastCheckList band b21=true := by decide +kernel

def b22 : List (Rectangle × FastWitness) := [(r176,⟨61,51,51⟩),(r177,⟨61,51,51⟩),(r178,⟨61,51,51⟩),(r179,⟨61,51,51⟩),(r180,⟨61,51,51⟩),(r181,⟨61,51,51⟩),(r182,⟨61,51,51⟩),(r183,⟨61,51,51⟩)]
theorem checked22 : fastCheckList band b22=true := by decide +kernel

def b23 : List (Rectangle × FastWitness) := [(r184,⟨61,51,51⟩),(r185,⟨61,51,51⟩),(r186,⟨61,51,51⟩),(r187,⟨61,51,51⟩),(r188,⟨61,51,52⟩),(r189,⟨61,52,52⟩),(r190,⟨61,52,52⟩),(r191,⟨61,52,52⟩)]
theorem checked23 : fastCheckList band b23=true := by decide +kernel

def b24 : List (Rectangle × FastWitness) := [(r192,⟨61,52,52⟩),(r193,⟨61,52,52⟩),(r194,⟨61,52,52⟩),(r195,⟨61,52,52⟩),(r196,⟨61,52,52⟩),(r197,⟨61,52,52⟩),(r198,⟨61,52,52⟩),(r199,⟨61,52,52⟩)]
theorem checked24 : fastCheckList band b24=true := by decide +kernel

def b25 : List (Rectangle × FastWitness) := [(r200,⟨61,52,52⟩),(r201,⟨61,52,52⟩),(r202,⟨61,52,52⟩),(r203,⟨61,52,52⟩),(r204,⟨61,52,52⟩),(r205,⟨61,52,52⟩),(r206,⟨61,53,53⟩),(r207,⟨61,53,53⟩)]
theorem checked25 : fastCheckList band b25=true := by decide +kernel

def b26 : List (Rectangle × FastWitness) := [(r208,⟨61,53,53⟩),(r209,⟨61,53,53⟩),(r210,⟨61,53,53⟩),(r211,⟨61,53,53⟩),(r212,⟨61,56,56⟩),(r213,⟨61,56,56⟩),(r214,⟨61,56,56⟩),(r215,⟨61,56,56⟩)]
theorem checked26 : fastCheckList band b26=true := by decide +kernel

def b27 : List (Rectangle × FastWitness) := [(r216,⟨61,56,56⟩),(r217,⟨61,56,56⟩),(r218,⟨61,56,56⟩),(r219,⟨61,56,56⟩),(r220,⟨61,56,56⟩),(r221,⟨61,56,56⟩),(r222,⟨61,56,56⟩),(r223,⟨61,56,56⟩)]
theorem checked27 : fastCheckList band b27=true := by decide +kernel

def b28 : List (Rectangle × FastWitness) := [(r224,⟨61,56,56⟩),(r225,⟨61,56,56⟩),(r226,⟨61,56,56⟩),(r227,⟨61,56,56⟩),(r228,⟨61,57,57⟩),(r229,⟨61,57,57⟩),(r230,⟨61,57,57⟩),(r231,⟨61,57,57⟩)]
theorem checked28 : fastCheckList band b28=true := by decide +kernel

def b29 : List (Rectangle × FastWitness) := [(r232,⟨61,57,57⟩),(r233,⟨61,57,57⟩),(r234,⟨61,57,57⟩),(r235,⟨61,57,57⟩),(r236,⟨61,57,57⟩)]
theorem checked29 : fastCheckList band b29=true := by decide +kernel

def witnessedRows : List (Rectangle × FastWitness) := b0++b1++b2++b3++b4++b5++b6++b7++b8++b9++b10++b11++b12++b13++b14++b15++b16++b17++b18++b19++b20++b21++b22++b23++b24++b25++b26++b27++b28++b29
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
  have joined25 := joinChecked _ _ joined24 checked25
  have joined26 := joinChecked _ _ joined25 checked26
  have joined27 := joinChecked _ _ joined26 checked27
  have joined28 := joinChecked _ _ joined27 checked28
  have joined29 := joinChecked _ _ joined28 checked29
  exact joined29
theorem all_checked : checkList band rows=true := fastCheckList_sound band witnessedRows all_fast_checked
theorem tiled : covers (minimumWeight band) (tail band) rows=true := by decide +kernel
theorem verified : VerifiedCover band rows :=
  ⟨all_checked,tiled,by decide +kernel⟩

open MvPolynomial RCN100 RCN119 ContactOrderBridge
open RCN234 (wt)
variable (K I : Type) [Field K] [CharP K 2130706433] [Fintype I] [DecidableEq I]
local instance  _root_.ProximityPrize.SubmissionLower.RelativeCertR12B49T3885To3924Fast.instDecidableEq_proximityPrize : DecidableEq K := Classical.decEq K

theorem regular_count {DF T nu : ℕ} {H : Poly4 K} (F : RCN266.RegularIndex H)
    (hbox : F.val∈globalCoefficientBox K DF 1 T 12)
    (hcode : wt (RCN081.contactWeights 131071) F.val=nu)
    (htotal : T≤wt RCN156.residualTotalWeights F.val)
    (hslope : 12≤wt RCN156.residualSWeights F.val)
    (hB : wt RCN156.residualYSWeights F.val≤49)
    (hT0 : 3885≤T) (hT1 : T≤3924) (hnu : 6422467≤nu)
    (nodes : I ↪ K) (u0 u1 : I → K) (hcard : Fintype.card I=262144)
    (selected : K → Polynomial K) (Gamma : Finset K)
    (hdegree : ∀ gamma∈Gamma, (selected gamma).natDegree≤131071)
    (hagreement : ∀ gamma∈Gamma, 181255≤
      ((Finset.univ : Finset I).filter (fun i => (selected gamma).eval (nodes i)=u0 i+gamma*u1 i)).card)
    (hno : RCN238.NoLargeSelectedPencil selected Gamma 131071 80889) :
    (RCN140.regularSeeds H selected Gamma F).card≤11380060537880462 :=
  regular_count_of_cover K I band rows verified F hbox hcode htotal hslope hB hT0 hT1 hnu
    nodes u0 u1 hcard selected Gamma hdegree hagreement hno



end
end ProximityPrize.SubmissionLower.RelativeCertR12B49T3885To3924Fast


