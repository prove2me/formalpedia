-- Prove2me | Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans085
-- name    : Sensitivity213981Formal_Endpoint22ReachPlans085
-- status  : Definition
-- author  : @yousofy
-- created : 2026-10-27T02:05:29.752876+00:00
-- url     : https://prove2.me/theorems/4125c2bd-ce86-44ab-82b2-4462e84dcaaf
-- title:
--   Endpoint22 Reach Plans085 — sensitivity certificate definitions
-- statement:
--   The definitions for Endpoint22 Reach Plans085 in the Boolean sensitivity construction. This interface preserves the data, predicates, finite structures, and essential constructor facts of the verified source module. All variables, indexing types, and numerical constants have the meanings specified by these definitions. The subsequent certificate theorems establish the required bounds; this interface adds no unproved assumptions.
--
--   The principal source declarations are `ThreeBoundEndpoint22Reachable.plan8229`, `ThreeBoundEndpoint22Reachable.plan8230`, `ThreeBoundEndpoint22Reachable.plan8231`, `ThreeBoundEndpoint22Reachable.plan8232`, `ThreeBoundEndpoint22Reachable.plan8233`, `ThreeBoundEndpoint22Reachable.plan8166`, `ThreeBoundEndpoint22Reachable.plan8234`, `ThreeBoundEndpoint22Reachable.plan8235`, `ThreeBoundEndpoint22Reachable.plan8236`, `ThreeBoundEndpoint22Reachable.plan8237`, `ThreeBoundEndpoint22Reachable.plan8238`, `ThreeBoundEndpoint22Reachable.plan8239`, together with the remaining tabulated data in this module.
-- source:
--   https://chatgpt.com/library?file_id=libfile_431310a5a24c81918d3f7bda6cf4262b&account_id=personal; verified archive SHA-256 15679de91204c2f0619380925cb21f560610f5a2467627ac5de8715f34ff3ddd; Endpoint22ReachPlans085.lean, lines 1–204.

import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits012
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachBits013
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachChoices
import Definitions.Def_Sensitivity213981Formal_Endpoint22ReachPlans064
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Sort
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Prod.Lex
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 2000000
set_option Elab.async false
namespace ThreeBoundEndpoint22Reachable
open ThreeBoundRelaxedReachable ThreeBoundRelaxed
open ThreeBoundRelaxedCompiled (Int3)
def plan8161 : Plan := .step choices269 bits1629 plan6190

def plan8162 : Plan := .step choices269 bits1625 plan6192

def plan8163 : Plan := .step choices269 bits1627 plan6193

def plan8164 : Plan := .step choices269 bits1625 plan6194

def plan8165 : Plan := .step choices269 bits1628 plan6195

def plan8166 : Plan := .step choices269 bits1627 plan6196

def plan8167 : Plan := .step choices269 bits1625 plan6197

def plan8168 : Plan := .step choices270 bits1641 plan6161

def plan8169 : Plan := .step choices270 bits1642 plan6162

def plan8170 : Plan := .step choices270 bits1641 plan6163

def plan8171 : Plan := .step choices270 bits1643 plan6164

def plan8172 : Plan := .step choices270 bits1642 plan6165

def plan8173 : Plan := .step choices270 bits1641 plan6166

def plan8174 : Plan := .step choices270 bits1644 plan6167

def plan8175 : Plan := .step choices270 bits1643 plan6168

def plan8176 : Plan := .step choices270 bits1642 plan6169

def plan8177 : Plan := .step choices270 bits1641 plan6170

def plan8178 : Plan := .step choices270 bits1630 plan6175

def plan8179 : Plan := .step choices270 bits1631 plan6176

def plan8180 : Plan := .step choices270 bits1630 plan6177

def plan8181 : Plan := .step choices270 bits1632 plan6178

def plan8182 : Plan := .step choices270 bits1631 plan6179

def plan8183 : Plan := .step choices270 bits1630 plan6180

def plan8184 : Plan := .step choices270 bits1633 plan6181

def plan8185 : Plan := .step choices270 bits1632 plan6182

def plan8186 : Plan := .step choices270 bits1631 plan6183

def plan8187 : Plan := .step choices270 bits1630 plan6184

def plan8188 : Plan := .step choices270 bits1634 plan6185

def plan8189 : Plan := .step choices270 bits1633 plan6186

def plan8190 : Plan := .step choices270 bits1632 plan6187

def plan8191 : Plan := .step choices270 bits1631 plan6188

def plan8192 : Plan := .step choices270 bits1630 plan6189

def plan8193 : Plan := .step choices270 bits1635 plan6190

def plan8194 : Plan := .step choices270 bits1634 plan6195

def plan8195 : Plan := .step choices270 bits1633 plan6196

def plan8196 : Plan := .step choices270 bits1632 plan6197

def plan8197 : Plan := .step choices270 bits1631 plan6198

def plan8198 : Plan := .step choices270 bits1630 plan6199

def plan8199 : Plan := .step choices271 bits1626 plan6167

def plan8200 : Plan := .step choices272 bits1641 plan6158

def plan8201 : Plan := .step choices272 bits1642 plan6159

def plan8202 : Plan := .step choices272 bits1641 plan6160

def plan8203 : Plan := .step choices272 bits1631 plan6162

def plan8204 : Plan := .step choices272 bits1632 plan6164

def plan8205 : Plan := .step choices272 bits1631 plan6165

def plan8206 : Plan := .step choices272 bits1633 plan6167

def plan8207 : Plan := .step choices272 bits1632 plan6168

def plan8208 : Plan := .step choices272 bits1631 plan6169

def plan8209 : Plan := .step choices272 bits1631 plan6171

def plan8210 : Plan := .step choices272 bits1631 plan6191

def plan8211 : Plan := .step choices275 bits1626 plan6167

def plan8212 : Plan := .step choices276 bits1641 plan6158

def plan8213 : Plan := .step choices276 bits1642 plan6159

def plan8214 : Plan := .step choices276 bits1641 plan6160

def plan8215 : Plan := .step choices276 bits1631 plan6162

def plan8216 : Plan := .step choices276 bits1632 plan6164

def plan8217 : Plan := .step choices276 bits1631 plan6165

def plan8218 : Plan := .step choices276 bits1633 plan6167

def plan8219 : Plan := .step choices276 bits1632 plan6168

def plan8220 : Plan := .step choices276 bits1631 plan6169

def plan8221 : Plan := .step choices276 bits1631 plan6191

def plan8222 : Plan := .step choices280 bits1707 plan6208

def plan8223 : Plan := .step choices280 bits1707 plan6216

def plan8224 : Plan := .step choices280 bits1708 plan6220

def plan8225 : Plan := .step choices280 bits1707 plan6221

def plan8226 : Plan := .step choices280 bits1709 plan6225

def plan8227 : Plan := .step choices280 bits1707 plan6228

def plan8228 : Plan := .step choices280 bits1708 plan6230

def plan8229 : Plan := .step choices280 bits1707 plan6231

def plan8230 : Plan := .step choices281 bits1710 plan6211

def plan8231 : Plan := .step choices281 bits1711 plan6213

def plan8232 : Plan := .step choices281 bits1710 plan6214

def plan8233 : Plan := .step choices281 bits1712 plan6216

def plan8234 : Plan := .step choices281 bits1711 plan6217

def plan8235 : Plan := .step choices281 bits1710 plan6218

def plan8236 : Plan := .step choices281 bits1713 plan6220

def plan8237 : Plan := .step choices281 bits1712 plan6221

def plan8238 : Plan := .step choices281 bits1711 plan6222

def plan8239 : Plan := .step choices281 bits1710 plan6223

def plan8240 : Plan := .step choices281 bits1714 plan6225

def plan8241 : Plan := .step choices281 bits1713 plan6230

def plan8242 : Plan := .step choices281 bits1712 plan6231

def plan8243 : Plan := .step choices281 bits1711 plan6232

def plan8244 : Plan := .step choices281 bits1710 plan6233

def plan8245 : Plan := .step choices282 bits1711 plan6203

def plan8246 : Plan := .step choices282 bits1699 plan6220

def plan8247 : Plan := .step choices282 bits1700 plan6225

def plan8248 : Plan := .step choices282 bits1699 plan6230

def plan8249 : Plan := .step choices283 bits1710 plan6200

def plan8250 : Plan := .step choices283 bits1711 plan6201

def plan8251 : Plan := .step choices283 bits1710 plan6202

def plan8252 : Plan := .step choices283 bits1712 plan6203

def plan8253 : Plan := .step choices283 bits1711 plan6204

def plan8254 : Plan := .step choices283 bits1710 plan6205

def plan8255 : Plan := .step choices283 bits1710 plan6206

def plan8256 : Plan := .step choices283 bits1698 plan6207

end ThreeBoundEndpoint22Reachable

end
end Sensitivity213981Formal


