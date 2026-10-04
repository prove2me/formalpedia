-- Prove2me | Definitions.Def_Yukon_d5f981dd1b98d3409f17e3a0
-- name    : Yukon_d5f981dd1b98d3409f17e3a0
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T07:58:17.573831+00:00
-- url     : https://prove2.me/theorems/91532330-6e22-4e7c-9eb7-12c0a5894e81
-- title:
--   YukonModule.ProximityPrize.SubmissionLower.WholeSpacePowerCover6814.part0
-- statement:
--   Source module ProximityPrize.SubmissionLower.WholeSpacePowerCover6814.
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/WholeSpacePowerCover6814.lean
--
--   yukon-proof-operation:certificate-r13-b54-2f3afc9323262ccfbd6534e7ff64b61ba4117907405d15b788ad05e366394f5f
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiZTNkZjZmMTQ0NWJhNTFlNzBmYmNmOTQ0NDhjYzEyNjYzZDg4MjFlMDQwMDc4MzZiN2ViMDE0OTA2NzM5ZTBlOSIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtMmYzYWZjOTMyMzI2MmNjZmJkNjUzNGU3ZmY2NGI2MWJhNDExNzkwNzQwNWQxNWI3ODhhZDA1ZTM2NjM5NGY1ZiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2Q1Zjk4MWRkMWI5OGQzNDA5ZjE3ZTNhMCIsInYiOjJ9]

import Definitions.Def_Yukon_6c577048bc498ec04b5f518e

import Definitions.Def_Yukon_4f169e935332851cf48361a5













































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Closed-form certificates and exhaustive arithmetic coverage for the small
source's native-failing nonlinear owners. No finite coefficient space is evaluated. -/
namespace ProximityPrize.SubmissionLower.WholeSpacePowerCover6814
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
open WholeSpacePowerBox6814 MovingSourceNativeEnvelope6814 RCN095 SecondJetRelaxedFlag

def Good (a : Box) : Prop := 131071*a.U≤a.C ∧ a.receipt<2*627003341034

def HasBox (q b u t : ℕ) : Prop := ∃ a : Box, a.q=q ∧ a.Covers b u t ∧ Good a

def box0 : Box := ⟨3,8,10,28,28⟩
theorem box0_good : Good box0 := by
  norm_num [Good,box0,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box1 : Box := ⟨3,9,10,24,131⟩
theorem box1_good : Good box1 := by
  norm_num [Good,box1,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box2 : Box := ⟨3,10,10,22,26⟩
theorem box2_good : Good box2 := by
  norm_num [Good,box2,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box3 : Box := ⟨2,15,15,47,319⟩
theorem box3_good : Good box3 := by
  norm_num [Good,box3,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box4 : Box := ⟨1,19,23,88,393⟩
theorem box4_good : Good box4 := by
  norm_num [Good,box4,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box5 : Box := ⟨1,22,31,86,86⟩
theorem box5_good : Good box5 := by
  norm_num [Good,box5,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box6 : Box := ⟨1,23,24,80,759⟩
theorem box6_good : Good box6 := by
  norm_num [Good,box6,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box7 : Box := ⟨1,24,24,78,908⟩
theorem box7_good : Good box7 := by
  norm_num [Good,box7,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box8 : Box := ⟨1,24,25,81,431⟩
theorem box8_good : Good box8 := by
  norm_num [Good,box8,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box9 : Box := ⟨1,25,25,74,848⟩
theorem box9_good : Good box9 := by
  norm_num [Good,box9,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box10 : Box := ⟨1,25,25,77,640⟩
theorem box10_good : Good box10 := by
  norm_num [Good,box10,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box11 : Box := ⟨1,25,26,80,223⟩
theorem box11_good : Good box11 := by
  norm_num [Good,box11,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box12 : Box := ⟨1,26,26,71,788⟩
theorem box12_good : Good box12 := by
  norm_num [Good,box12,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box13 : Box := ⟨1,26,26,74,580⟩
theorem box13_good : Good box13 := by
  norm_num [Good,box13,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box14 : Box := ⟨1,26,27,77,242⟩
theorem box14_good : Good box14 := by
  norm_num [Good,box14,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box15 : Box := ⟨1,26,31,78,78⟩
theorem box15_good : Good box15 := by
  norm_num [Good,box15,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box16 : Box := ⟨1,27,27,67,729⟩
theorem box16_good : Good box16 := by
  norm_num [Good,box16,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box17 : Box := ⟨1,27,27,71,451⟩
theorem box17_good : Good box17 := by
  norm_num [Good,box17,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box18 : Box := ⟨1,27,28,73,252⟩
theorem box18_good : Good box18 := by
  norm_num [Good,box18,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box19 : Box := ⟨1,28,29,63,540⟩
theorem box19_good : Good box19 := by
  norm_num [Good,box19,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box20 : Box := ⟨1,28,31,69,69⟩
theorem box20_good : Good box20 := by
  norm_num [Good,box20,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box21 : Box := ⟨1,29,31,59,331⟩
theorem box21_good : Good box21 := by
  norm_num [Good,box21,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def box22 : Box := ⟨1,30,31,51,65⟩
theorem box22_good : Good box22 := by
  norm_num [Good,box22,Box.receipt,Box.n,Box.R,Box.U,Box.T,Box.C]

def native (m s b u t : ℕ) : ℕ :=
  3*126275387074424400*m+
    coefficientZ3*flagMixed parentFlag unitZFlag (budgetFlag b u t m s)+
    coefficientU3*flagMixed parentFlag unitYZFlag (budgetFlag b u t m s)+
    coefficientA3*flagMixed parentFlag unitAllFlag (budgetFlag b u t m s)

theorem native_linear (m s b u t : ℕ) (hms : m≤s) (hsb : 2*s≤b)
    (hbu : b≤u) (hut : u≤t) :
    native m s b u t+67309222137259641*s =
      29746364480525841*b+7705577043726672*u+110916132481287*t+453951876536740800*m := by
  norm_num [native,coefficientZ3,coefficientU3,coefficientA3,parentFlag,
    budgetFlag,flagMixed,unitZFlag,unitYZFlag,unitAllFlag]
  omega

theorem cover1 (b u t : ℕ) (hb : b≤10) (hbu : b≤u)
    (hu : u≤32) (hut : u≤t) (ht : t≤331)
    (hfail : 496873814521953525≤29746364480525841*b+7705577043726672*u+110916132481287*t) :
    HasBox 3 b u t := by
  have hh : box0.Covers b u t ∨ box1.Covers b u t ∨ box2.Covers b u t := by
    dsimp [Box.Covers,box0,box1,box2]
    omega
  rcases hh with h0 | h1 | h2
  · exact ⟨box0,rfl,h0,box0_good⟩
  · exact ⟨box1,rfl,h1,box1_good⟩
  · exact ⟨box2,rfl,h2,box2_good⟩

theorem cover2 (b u t : ℕ) (hb : b≤15) (hbu : b≤u)
    (hu : u≤49) (hut : u≤t) (ht : t≤497)
    (hfail : 859129184769387768≤29746364480525841*b+7705577043726672*u+110916132481287*t) :
    HasBox 2 b u t := by
  have hh : box3.Covers b u t := by
    dsimp [Box.Covers,box3]
    omega
  exact ⟨box3,rfl,hh,box3_good⟩

public theorem cover3_b19 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*19+7705577043726672*u+110916132481287*t) :
    HasBox 1 19 u t := by
  have hh : box4.Covers 19 u t := by
    dsimp [Box.Covers,box4]
    omega
  exact ⟨box4,rfl,hh,box4_good⟩

public theorem cover3_b20 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*20+7705577043726672*u+110916132481287*t) :
    HasBox 1 20 u t := by
  have hh : box4.Covers 20 u t := by
    dsimp [Box.Covers,box4]
    omega
  exact ⟨box4,rfl,hh,box4_good⟩

public theorem cover3_b21 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*21+7705577043726672*u+110916132481287*t) :
    HasBox 1 21 u t := by
  have hh : box4.Covers 21 u t := by
    dsimp [Box.Covers,box4]
    omega
  exact ⟨box4,rfl,hh,box4_good⟩

public theorem cover3_b22 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*22+7705577043726672*u+110916132481287*t) :
    HasBox 1 22 u t := by
  have hh : box4.Covers 22 u t ∨ box5.Covers 22 u t := by
    dsimp [Box.Covers,box4,box5]
    omega
  rcases hh with h4 | h5
  · exact ⟨box4,rfl,h4,box4_good⟩
  · exact ⟨box5,rfl,h5,box5_good⟩

public theorem cover3_b23 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*23+7705577043726672*u+110916132481287*t) :
    HasBox 1 23 u t := by
  have hh : box4.Covers 23 u t ∨ box5.Covers 23 u t ∨ box6.Covers 23 u t := by
    dsimp [Box.Covers,box4,box5,box6]
    omega
  rcases hh with h4 | h5 | h6
  · exact ⟨box4,rfl,h4,box4_good⟩
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box6,rfl,h6,box6_good⟩

public theorem cover3_b24 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*24+7705577043726672*u+110916132481287*t) :
    HasBox 1 24 u t := by
  have hh : box5.Covers 24 u t ∨ box6.Covers 24 u t ∨ box7.Covers 24 u t ∨ box8.Covers 24 u t := by
    dsimp [Box.Covers,box5,box6,box7,box8]
    omega
  rcases hh with h5 | h6 | h7 | h8
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box6,rfl,h6,box6_good⟩
  · exact ⟨box7,rfl,h7,box7_good⟩
  · exact ⟨box8,rfl,h8,box8_good⟩

public theorem cover3_b25 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*25+7705577043726672*u+110916132481287*t) :
    HasBox 1 25 u t := by
  have hh : box5.Covers 25 u t ∨ box8.Covers 25 u t ∨ box9.Covers 25 u t ∨ box10.Covers 25 u t ∨ box11.Covers 25 u t := by
    dsimp [Box.Covers,box5,box8,box9,box10,box11]
    omega
  rcases hh with h5 | h8 | h9 | h10 | h11
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box8,rfl,h8,box8_good⟩
  · exact ⟨box9,rfl,h9,box9_good⟩
  · exact ⟨box10,rfl,h10,box10_good⟩
  · exact ⟨box11,rfl,h11,box11_good⟩

public theorem cover3_b26 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*26+7705577043726672*u+110916132481287*t) :
    HasBox 1 26 u t := by
  have hh : box5.Covers 26 u t ∨ box11.Covers 26 u t ∨ box12.Covers 26 u t ∨ box13.Covers 26 u t ∨ box14.Covers 26 u t ∨ box15.Covers 26 u t := by
    dsimp [Box.Covers,box5,box11,box12,box13,box14,box15]
    omega
  rcases hh with h5 | h11 | h12 | h13 | h14 | h15
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box11,rfl,h11,box11_good⟩
  · exact ⟨box12,rfl,h12,box12_good⟩
  · exact ⟨box13,rfl,h13,box13_good⟩
  · exact ⟨box14,rfl,h14,box14_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩

public theorem cover3_b27 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*27+7705577043726672*u+110916132481287*t) :
    HasBox 1 27 u t := by
  have hh : box5.Covers 27 u t ∨ box14.Covers 27 u t ∨ box15.Covers 27 u t ∨ box16.Covers 27 u t ∨ box17.Covers 27 u t ∨ box18.Covers 27 u t := by
    dsimp [Box.Covers,box5,box14,box15,box16,box17,box18]
    omega
  rcases hh with h5 | h14 | h15 | h16 | h17 | h18
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box14,rfl,h14,box14_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩
  · exact ⟨box16,rfl,h16,box16_good⟩
  · exact ⟨box17,rfl,h17,box17_good⟩
  · exact ⟨box18,rfl,h18,box18_good⟩

public theorem cover3_b28 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*28+7705577043726672*u+110916132481287*t) :
    HasBox 1 28 u t := by
  have hh : box5.Covers 28 u t ∨ box15.Covers 28 u t ∨ box18.Covers 28 u t ∨ box19.Covers 28 u t ∨ box20.Covers 28 u t := by
    dsimp [Box.Covers,box5,box15,box18,box19,box20]
    omega
  rcases hh with h5 | h15 | h18 | h19 | h20
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩
  · exact ⟨box18,rfl,h18,box18_good⟩
  · exact ⟨box19,rfl,h19,box19_good⟩
  · exact ⟨box20,rfl,h20,box20_good⟩

public theorem cover3_b29 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*29+7705577043726672*u+110916132481287*t) :
    HasBox 1 29 u t := by
  have hh : box5.Covers 29 u t ∨ box15.Covers 29 u t ∨ box19.Covers 29 u t ∨ box20.Covers 29 u t ∨ box21.Covers 29 u t := by
    dsimp [Box.Covers,box5,box15,box19,box20,box21]
    omega
  rcases hh with h5 | h15 | h19 | h20 | h21
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩
  · exact ⟨box19,rfl,h19,box19_good⟩
  · exact ⟨box20,rfl,h20,box20_good⟩
  · exact ⟨box21,rfl,h21,box21_good⟩

public theorem cover3_b30 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*30+7705577043726672*u+110916132481287*t) :
    HasBox 1 30 u t := by
  have hh : box5.Covers 30 u t ∨ box15.Covers 30 u t ∨ box20.Covers 30 u t ∨ box21.Covers 30 u t ∨ box22.Covers 30 u t := by
    dsimp [Box.Covers,box5,box15,box20,box21,box22]
    omega
  rcases hh with h5 | h15 | h20 | h21 | h22
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩
  · exact ⟨box20,rfl,h20,box20_good⟩
  · exact ⟨box21,rfl,h21,box21_good⟩
  · exact ⟨box22,rfl,h22,box22_good⟩

public theorem cover3_b31 (u t : ℕ) (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*31+7705577043726672*u+110916132481287*t) :
    HasBox 1 31 u t := by
  have hh : box5.Covers 31 u t ∨ box15.Covers 31 u t ∨ box20.Covers 31 u t ∨ box21.Covers 31 u t ∨ box22.Covers 31 u t := by
    dsimp [Box.Covers,box5,box15,box20,box21,box22]
    omega
  rcases hh with h5 | h15 | h20 | h21 | h22
  · exact ⟨box5,rfl,h5,box5_good⟩
  · exact ⟨box15,rfl,h15,box15_good⟩
  · exact ⟨box20,rfl,h20,box20_good⟩
  · exact ⟨box21,rfl,h21,box21_good⟩
  · exact ⟨box22,rfl,h22,box22_good⟩

theorem cover3 (b u t : ℕ) (hb : b≤31) (_hbu : b≤u)
    (hu : u≤98) (hut : u≤t) (ht : t≤995)
    (hfail : 1423312221428600934≤29746364480525841*b+7705577043726672*u+110916132481287*t) :
    HasBox 1 b u t := by
  have hb19 : 19≤b := by omega
  interval_cases b
  · exact cover3_b19 u t hu hut ht hfail
  · exact cover3_b20 u t hu hut ht hfail
  · exact cover3_b21 u t hu hut ht hfail
  · exact cover3_b22 u t hu hut ht hfail
  · exact cover3_b23 u t hu hut ht hfail
  · exact cover3_b24 u t hu hut ht hfail
  · exact cover3_b25 u t hu hut ht hfail
  · exact cover3_b26 u t hu hut ht hfail
  · exact cover3_b27 u t hu hut ht hfail
  · exact cover3_b28 u t hu hut ht hfail
  · exact cover3_b29 u t hu hut ht hfail
  · exact cover3_b30 u t hu hut ht hfail
  · exact cover3_b31 u t hu hut ht hfail











end
end ProximityPrize.SubmissionLower.WholeSpacePowerCover6814


