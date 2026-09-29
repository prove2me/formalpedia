-- Prove2me | solution 1 for AutomorphicForm.isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/997c2483-9ef2-5608-8ef3-55408c5e379a

import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel
import Theorems.Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
p2m_attr_erase "simp" "AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace Ws14KN

theorem isClosed_principalLevel (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsClosed (principalLevel (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F)) := by
  have h1 : IsClosed (levelOne (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F)) := isClosed_levelOne (𝓞 F) F N
  have h2 : IsClosed ((fun g => (weyl (𝓞 F) F)⁻¹ * g * weyl (𝓞 F) F) ⁻¹' (levelOne (𝓞 F) F N : Set (AdelicGL2 (𝓞 F) F))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  rw [mem_principalLevel_iff, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

end Ws14KN

theorem solution
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  refine (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup F N).of_isClosed_subset ?_ ?_
  · rw [Subgroup.coe_inf]
    exact (Ws14KN.isClosed_principalLevel F N).inter (isClosed_finiteAdelicGL2Subgroup F)
  · rw [Subgroup.coe_inf, Subgroup.coe_inf]
    exact Set.inter_subset_inter_left _ (principalLevel_le_levelOne (𝓞 F) F N)

end S_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup
end P2MW
export P2MW.S_AutomorphicForm_isCompact_principalLevel_inf_finiteAdelicGL2Subgroup (solution)
