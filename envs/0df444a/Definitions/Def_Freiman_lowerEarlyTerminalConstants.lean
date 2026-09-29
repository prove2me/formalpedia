-- Prove2me | Definitions.Def_Freiman_lowerEarlyTerminalConstants
-- name    : Freiman_lowerEarlyTerminalConstants
-- status  : Definition
-- author  : @tp
-- created : 2026-09-09T13:23:13.731451+00:00
-- url     : https://prove2.me/theorems/fa60ce73-beee-486d-823c-00fa35aa30ae
-- title:
--   Freiman.lowerEarlyTerminalConstants
-- statement:
--   Exact Q(√3,√7) values of H7,H18,H27,H34,A9,D40,D44,D46 from the report scalar threshold table. Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), pp.120–132, §§ s15:early-residual and s15:terminal-extension; pp.133–139, Proposition l139chain and Appendix app:l139cert. Source: certificates/section15_early/{residual_geometry_certificate,extension_1,extension_2}.json and certificates/section15_terminal/geometry_certificate.json; PROOF_GUIDE.md; verification/families/section15_early/{independent_residual,independent_extensions}.py and section15_terminal/verify_independent.py. Lean module: Definitions.Def_Freiman_lowerEarlyTerminalConstants.

import Definitions.Def_Freiman_lowerEarlyTerminalModel
namespace Freiman
def lowerEarlyTerminalH7 : CertBound := ⟨true,false,⟨⟨(31/100),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨2,-1,0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
def lowerEarlyTerminalH18 : CertBound := ⟨false,false,⟨⟨(183/250),0,0,0⟩,⟨(5/22),(1/22),0,0⟩,⟨(15/37),(-1/37),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
def lowerEarlyTerminalH27 : CertBound := ⟨false,false,⟨⟨(1703/253),(-884/253),0,0⟩,⟨(10/23),(-1/69),0,0⟩,⟨(5/11),(-1/11),0,0⟩,⟨(3/13),(1/39),0,0⟩,⟨(4/13),(1/13),0,0⟩⟩⟩
def lowerEarlyTerminalH34 : CertBound := ⟨false,false,⟨⟨(153/250),0,0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(35/94),(1/94),0,0⟩,⟨(-1/10),0,0,(1/10)⟩,⟨(5/22),(1/22),0,0⟩⟩⟩
def lowerEarlyTerminalD40 : CertBound := ⟨true,false,⟨⟨(669/1406),0,0,(109/29526)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(3/10),0,0,(1/70)⟩,⟨(121/430),0,0,(-1/430)⟩,⟨(121/430),0,0,(-1/430)⟩⟩⟩
def lowerEarlyTerminalD44 : CertBound := ⟨true,false,⟨⟨(1355921/3029375),0,0,(-33236/3029375)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(3539/9250),0,0,(1/9250)⟩,⟨(31/94),0,0,(-1/94)⟩,⟨(31/94),0,0,(-1/94)⟩⟩⟩
def lowerEarlyTerminalD46 : CertBound := ⟨true,false,⟨⟨(-24300/147323),(51497/147323),0,0⟩,⟨(247/649),(1/649),0,0⟩,⟨(177/454),(-1/454),0,0⟩,⟨(16/59),(1/177),0,0⟩,⟨(133/478),(-1/478),0,0⟩⟩⟩
def lowerEarlyTerminalA9 : CertBound := ⟨false,false,⟨⟨(3/2),(-1/2),0,0⟩,⟨(-1/2),(1/2),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(4/13),(1/13),0,0⟩,⟨(9/13),(-1/13),0,0⟩⟩⟩
end Freiman


