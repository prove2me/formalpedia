-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree22
-- name    : CK_GeneralCK_Certificates_ReflectionSmallBiasContactDegree22
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T23:07:13.826814+00:00
-- url     : https://prove2.me/theorems/309fb5f3-249f-4694-a281-be0735689aec
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree22` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree22` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.ReflectionSmallBiasContactDegree22` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.ReflectionSmallBiasContactDegree22 (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/ReflectionSmallBiasContactDegree22.lean)

import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasHalfSumPowers
import Definitions.Def_CK_GeneralCK_Certificates_ReflectionSmallBiasBivariateInverse21
import Definitions.Def_CK_GeneralCK_ReflectionSmallBiasPerspectiveJet

-- ===== source module GeneralCK.Certificates.ReflectionSmallBiasContactDegree22 =====
section

namespace GeneralCK.Reflection.SmallBiasContactDegrees

open SmallBiasPolynomial SmallBiasJet SmallBiasPerspectiveJet
open SmallBiasHalfSumPowers SmallBiasBivariateBase SmallBiasBivariateInverse

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def phiGroup22 : List Term :=
  [⟨22, 0, 11, (4199 / 128 : ℚ)⟩,
   ⟨22, 0, 12, (-104975 / 768 : ℚ)⟩,
   ⟨22, 0, 13, (13243 / 48 : ℚ)⟩,
   ⟨22, 0, 14, (-1428629 / 4032 : ℚ)⟩,
   ⟨22, 0, 15, (6443527 / 20160 : ℚ)⟩,
   ⟨22, 0, 16, (-480907271 / 2280960 : ℚ)⟩,
   ⟨22, 0, 17, (62104730741 / 605404800 : ℚ)⟩,
   ⟨22, 0, 18, (-4696047353 / 129729600 : ℚ)⟩,
   ⟨22, 0, 19, (6813700429 / 771891120 : ℚ)⟩,
   ⟨22, 0, 20, (-155685007 / 116396280 : ℚ)⟩,
   ⟨22, 0, 21, (2 / 21 : ℚ)⟩]

def coefficient22 : List Term :=
  [⟨0, 0, 11, (4199 / 128 : ℚ)⟩,
   ⟨0, 0, 12, (-104975 / 768 : ℚ)⟩,
   ⟨0, 0, 13, (13243 / 48 : ℚ)⟩,
   ⟨0, 0, 14, (-1428629 / 4032 : ℚ)⟩,
   ⟨0, 0, 15, (6443527 / 20160 : ℚ)⟩,
   ⟨0, 0, 16, (-480907271 / 2280960 : ℚ)⟩,
   ⟨0, 0, 17, (62104730741 / 605404800 : ℚ)⟩,
   ⟨0, 0, 18, (-4696047353 / 129729600 : ℚ)⟩,
   ⟨0, 0, 19, (6813700429 / 771891120 : ℚ)⟩,
   ⟨0, 0, 20, (-155685007 / 116396280 : ℚ)⟩,
   ⟨0, 0, 21, (2 / 21 : ℚ)⟩]

def body22 : List Term :=
  [⟨0, 22, -21, (1 / 4194304 : ℚ)⟩,
   ⟨1, 21, -21, (11 / 2097152 : ℚ)⟩,
   ⟨2, 20, -21, (231 / 4194304 : ℚ)⟩,
   ⟨3, 19, -21, (385 / 1048576 : ℚ)⟩,
   ⟨4, 18, -21, (7315 / 4194304 : ℚ)⟩,
   ⟨5, 17, -21, (13167 / 2097152 : ℚ)⟩,
   ⟨6, 16, -21, (74613 / 4194304 : ℚ)⟩,
   ⟨7, 15, -21, (10659 / 262144 : ℚ)⟩,
   ⟨8, 14, -21, (159885 / 2097152 : ℚ)⟩,
   ⟨9, 13, -21, (124355 / 1048576 : ℚ)⟩,
   ⟨10, 12, -21, (323323 / 2097152 : ℚ)⟩,
   ⟨11, 11, -21, (88179 / 524288 : ℚ)⟩,
   ⟨12, 10, -21, (323323 / 2097152 : ℚ)⟩,
   ⟨13, 9, -21, (124355 / 1048576 : ℚ)⟩,
   ⟨14, 8, -21, (159885 / 2097152 : ℚ)⟩,
   ⟨15, 7, -21, (10659 / 262144 : ℚ)⟩,
   ⟨16, 6, -21, (74613 / 4194304 : ℚ)⟩,
   ⟨17, 5, -21, (13167 / 2097152 : ℚ)⟩,
   ⟨18, 4, -21, (7315 / 4194304 : ℚ)⟩,
   ⟨19, 3, -21, (385 / 1048576 : ℚ)⟩,
   ⟨20, 2, -21, (231 / 4194304 : ℚ)⟩,
   ⟨21, 1, -21, (11 / 2097152 : ℚ)⟩,
   ⟨22, 0, -21, (1 / 4194304 : ℚ)⟩]

def group22 : List Term :=
  [⟨0, 22, -10, (4199 / 536870912 : ℚ)⟩,
   ⟨0, 22, -9, (-104975 / 3221225472 : ℚ)⟩,
   ⟨0, 22, -8, (13243 / 201326592 : ℚ)⟩,
   ⟨0, 22, -7, (-1428629 / 16911433728 : ℚ)⟩,
   ⟨0, 22, -6, (6443527 / 84557168640 : ℚ)⟩,
   ⟨0, 22, -5, (-480907271 / 9567039651840 : ℚ)⟩,
   ⟨0, 22, -4, (62104730741 / 2539251774259200 : ℚ)⟩,
   ⟨0, 22, -3, (-4696047353 / 544125380198400 : ℚ)⟩,
   ⟨0, 22, -2, (6813700429 / 3237546012180480 : ℚ)⟩,
   ⟨0, 22, -1, (-155685007 / 488201382789120 : ℚ)⟩,
   ⟨0, 22, 0, (1 / 44040192 : ℚ)⟩,
   ⟨1, 21, -10, (46189 / 268435456 : ℚ)⟩,
   ⟨1, 21, -9, (-1154725 / 1610612736 : ℚ)⟩,
   ⟨1, 21, -8, (145673 / 100663296 : ℚ)⟩,
   ⟨1, 21, -7, (-15714919 / 8455716864 : ℚ)⟩,
   ⟨1, 21, -6, (70878797 / 42278584320 : ℚ)⟩,
   ⟨1, 21, -5, (-480907271 / 434865438720 : ℚ)⟩,
   ⟨1, 21, -4, (62104730741 / 115420535193600 : ℚ)⟩,
   ⟨1, 21, -3, (-4696047353 / 24732971827200 : ℚ)⟩,
   ⟨1, 21, -2, (6813700429 / 147161182371840 : ℚ)⟩,
   ⟨1, 21, -1, (-155685007 / 22190971944960 : ℚ)⟩,
   ⟨1, 21, 0, (11 / 22020096 : ℚ)⟩,
   ⟨2, 20, -10, (969969 / 536870912 : ℚ)⟩,
   ⟨2, 20, -9, (-8083075 / 1073741824 : ℚ)⟩,
   ⟨2, 20, -8, (1019711 / 67108864 : ℚ)⟩,
   ⟨2, 20, -7, (-15714919 / 805306368 : ℚ)⟩,
   ⟨2, 20, -6, (70878797 / 4026531840 : ℚ)⟩,
   ⟨2, 20, -5, (-3366350897 / 289910292480 : ℚ)⟩,
   ⟨2, 20, -4, (62104730741 / 10992431923200 : ℚ)⟩,
   ⟨2, 20, -3, (-4696047353 / 2355521126400 : ℚ)⟩,
   ⟨2, 20, -2, (6813700429 / 14015350702080 : ℚ)⟩,
   ⟨2, 20, -1, (-155685007 / 2113425899520 : ℚ)⟩,
   ⟨2, 20, 0, (11 / 2097152 : ℚ)⟩,
   ⟨3, 19, -10, (1616615 / 134217728 : ℚ)⟩,
   ⟨3, 19, -9, (-40415375 / 805306368 : ℚ)⟩,
   ⟨3, 19, -8, (5098555 / 50331648 : ℚ)⟩,
   ⟨3, 19, -7, (-78574595 / 603979776 : ℚ)⟩,
   ⟨3, 19, -6, (70878797 / 603979776 : ℚ)⟩,
   ⟨3, 19, -5, (-3366350897 / 43486543872 : ℚ)⟩,
   ⟨3, 19, -4, (62104730741 / 1648864788480 : ℚ)⟩,
   ⟨3, 19, -3, (-4696047353 / 353328168960 : ℚ)⟩,
   ⟨3, 19, -2, (6813700429 / 2102302605312 : ℚ)⟩,
   ⟨3, 19, -1, (-155685007 / 317013884928 : ℚ)⟩,
   ⟨3, 19, 0, (55 / 1572864 : ℚ)⟩,
   ⟨4, 18, -10, (30715685 / 536870912 : ℚ)⟩,
   ⟨4, 18, -9, (-767892125 / 3221225472 : ℚ)⟩,
   ⟨4, 18, -8, (96872545 / 201326592 : ℚ)⟩,
   ⟨4, 18, -7, (-1492917305 / 2415919104 : ℚ)⟩,
   ⟨4, 18, -6, (1346697143 / 2415919104 : ℚ)⟩,
   ⟨4, 18, -5, (-63960667043 / 173946175488 : ℚ)⟩,
   ⟨4, 18, -4, (1179989884079 / 6595459153920 : ℚ)⟩,
   ⟨4, 18, -3, (-89224899707 / 1413312675840 : ℚ)⟩,
   ⟨4, 18, -2, (129460308151 / 8409210421248 : ℚ)⟩,
   ⟨4, 18, -1, (-155685007 / 66739765248 : ℚ)⟩,
   ⟨4, 18, 0, (1045 / 6291456 : ℚ)⟩,
   ⟨5, 17, -10, (55288233 / 268435456 : ℚ)⟩,
   ⟨5, 17, -9, (-460735275 / 536870912 : ℚ)⟩,
   ⟨5, 17, -8, (58123527 / 33554432 : ℚ)⟩,
   ⟨5, 17, -7, (-298583461 / 134217728 : ℚ)⟩,
   ⟨5, 17, -6, (1346697143 / 671088640 : ℚ)⟩,
   ⟨5, 17, -5, (-63960667043 / 48318382080 : ℚ)⟩,
   ⟨5, 17, -4, (1179989884079 / 1832071987200 : ℚ)⟩,
   ⟨5, 17, -3, (-89224899707 / 392586854400 : ℚ)⟩,
   ⟨5, 17, -2, (129460308151 / 2335891783680 : ℚ)⟩,
   ⟨5, 17, -1, (-155685007 / 18538823680 : ℚ)⟩,
   ⟨5, 17, 0, (627 / 1048576 : ℚ)⟩,
   ⟨6, 16, -10, (313299987 / 536870912 : ℚ)⟩,
   ⟨6, 16, -9, (-2610833225 / 1073741824 : ℚ)⟩,
   ⟨6, 16, -8, (329366653 / 67108864 : ℚ)⟩,
   ⟨6, 16, -7, (-5075918837 / 805306368 : ℚ)⟩,
   ⟨6, 16, -6, (22893851431 / 4026531840 : ℚ)⟩,
   ⟨6, 16, -5, (-1087331339731 / 289910292480 : ℚ)⟩,
   ⟨6, 16, -4, (20059828029343 / 10992431923200 : ℚ)⟩,
   ⟨6, 16, -3, (-1516823295019 / 2355521126400 : ℚ)⟩,
   ⟨6, 16, -2, (129460308151 / 824432394240 : ℚ)⟩,
   ⟨6, 16, -1, (-155685007 / 6543114240 : ℚ)⟩,
   ⟨6, 16, 0, (3553 / 2097152 : ℚ)⟩,
   ⟨7, 15, -10, (44757141 / 33554432 : ℚ)⟩,
   ⟨7, 15, -9, (-372976175 / 67108864 : ℚ)⟩,
   ⟨7, 15, -8, (47052379 / 4194304 : ℚ)⟩,
   ⟨7, 15, -7, (-5075918837 / 352321536 : ℚ)⟩,
   ⟨7, 15, -6, (22893851431 / 1761607680 : ℚ)⟩,
   ⟨7, 15, -5, (-155333048533 / 18119393280 : ℚ)⟩,
   ⟨7, 15, -4, (20059828029343 / 4809188966400 : ℚ)⟩,
   ⟨7, 15, -3, (-1516823295019 / 1030540492800 : ℚ)⟩,
   ⟨7, 15, -2, (129460308151 / 360689172480 : ℚ)⟩,
   ⟨7, 15, -1, (-155685007 / 2862612480 : ℚ)⟩,
   ⟨7, 15, 0, (3553 / 917504 : ℚ)⟩,
   ⟨8, 14, -10, (671357115 / 268435456 : ℚ)⟩,
   ⟨8, 14, -9, (-5594642625 / 536870912 : ℚ)⟩,
   ⟨8, 14, -8, (705785685 / 33554432 : ℚ)⟩,
   ⟨8, 14, -7, (-25379594185 / 939524096 : ℚ)⟩,
   ⟨8, 14, -6, (22893851431 / 939524096 : ℚ)⟩,
   ⟨8, 14, -5, (-155333048533 / 9663676416 : ℚ)⟩,
   ⟨8, 14, -4, (20059828029343 / 2564900782080 : ℚ)⟩,
   ⟨8, 14, -3, (-1516823295019 / 549621596160 : ℚ)⟩,
   ⟨8, 14, -2, (129460308151 / 192367558656 : ℚ)⟩,
   ⟨8, 14, -1, (-155685007 / 1526726656 : ℚ)⟩,
   ⟨8, 14, 0, (53295 / 7340032 : ℚ)⟩,
   ⟨9, 13, -10, (522166645 / 134217728 : ℚ)⟩,
   ⟨9, 13, -9, (-13054166125 / 805306368 : ℚ)⟩,
   ⟨9, 13, -8, (1646833265 / 50331648 : ℚ)⟩,
   ⟨9, 13, -7, (-25379594185 / 603979776 : ℚ)⟩,
   ⟨9, 13, -6, (22893851431 / 603979776 : ℚ)⟩,
   ⟨9, 13, -5, (-1087331339731 / 43486543872 : ℚ)⟩,
   ⟨9, 13, -4, (20059828029343 / 1648864788480 : ℚ)⟩,
   ⟨9, 13, -3, (-1516823295019 / 353328168960 : ℚ)⟩,
   ⟨9, 13, -2, (129460308151 / 123664859136 : ℚ)⟩,
   ⟨9, 13, -1, (-155685007 / 981467136 : ℚ)⟩,
   ⟨9, 13, 0, (17765 / 1572864 : ℚ)⟩,
   ⟨10, 12, -10, (1357633277 / 268435456 : ℚ)⟩,
   ⟨10, 12, -9, (-33940831925 / 1610612736 : ℚ)⟩,
   ⟨10, 12, -8, (4281766489 / 100663296 : ℚ)⟩,
   ⟨10, 12, -7, (-65986944881 / 1207959552 : ℚ)⟩,
   ⟨10, 12, -6, (297620068603 / 6039797760 : ℚ)⟩,
   ⟨10, 12, -5, (-14135307416503 / 434865438720 : ℚ)⟩,
   ⟨10, 12, -4, (20059828029343 / 1268357529600 : ℚ)⟩,
   ⟨10, 12, -3, (-1516823295019 / 271790899200 : ℚ)⟩,
   ⟨10, 12, -2, (129460308151 / 95126814720 : ℚ)⟩,
   ⟨10, 12, -1, (-155685007 / 754974720 : ℚ)⟩,
   ⟨10, 12, 0, (46189 / 3145728 : ℚ)⟩,
   ⟨11, 11, -10, (370263621 / 67108864 : ℚ)⟩,
   ⟨11, 11, -9, (-3085530175 / 134217728 : ℚ)⟩,
   ⟨11, 11, -8, (389251499 / 8388608 : ℚ)⟩,
   ⟨11, 11, -7, (-5998813171 / 100663296 : ℚ)⟩,
   ⟨11, 11, -6, (27056369873 / 503316480 : ℚ)⟩,
   ⟨11, 11, -5, (-14135307416503 / 398626652160 : ℚ)⟩,
   ⟨11, 11, -4, (20059828029343 / 1162661068800 : ℚ)⟩,
   ⟨11, 11, -3, (-1516823295019 / 249141657600 : ℚ)⟩,
   ⟨11, 11, -2, (129460308151 / 87199580160 : ℚ)⟩,
   ⟨11, 11, -1, (-155685007 / 692060160 : ℚ)⟩,
   ⟨11, 11, 0, (4199 / 262144 : ℚ)⟩,
   ⟨12, 10, -10, (1357633277 / 268435456 : ℚ)⟩,
   ⟨12, 10, -9, (-33940831925 / 1610612736 : ℚ)⟩,
   ⟨12, 10, -8, (4281766489 / 100663296 : ℚ)⟩,
   ⟨12, 10, -7, (-65986944881 / 1207959552 : ℚ)⟩,
   ⟨12, 10, -6, (297620068603 / 6039797760 : ℚ)⟩,
   ⟨12, 10, -5, (-14135307416503 / 434865438720 : ℚ)⟩,
   ⟨12, 10, -4, (20059828029343 / 1268357529600 : ℚ)⟩,
   ⟨12, 10, -3, (-1516823295019 / 271790899200 : ℚ)⟩,
   ⟨12, 10, -2, (129460308151 / 95126814720 : ℚ)⟩,
   ⟨12, 10, -1, (-155685007 / 754974720 : ℚ)⟩,
   ⟨12, 10, 0, (46189 / 3145728 : ℚ)⟩,
   ⟨13, 9, -10, (522166645 / 134217728 : ℚ)⟩,
   ⟨13, 9, -9, (-13054166125 / 805306368 : ℚ)⟩,
   ⟨13, 9, -8, (1646833265 / 50331648 : ℚ)⟩,
   ⟨13, 9, -7, (-25379594185 / 603979776 : ℚ)⟩,
   ⟨13, 9, -6, (22893851431 / 603979776 : ℚ)⟩,
   ⟨13, 9, -5, (-1087331339731 / 43486543872 : ℚ)⟩,
   ⟨13, 9, -4, (20059828029343 / 1648864788480 : ℚ)⟩,
   ⟨13, 9, -3, (-1516823295019 / 353328168960 : ℚ)⟩,
   ⟨13, 9, -2, (129460308151 / 123664859136 : ℚ)⟩,
   ⟨13, 9, -1, (-155685007 / 981467136 : ℚ)⟩,
   ⟨13, 9, 0, (17765 / 1572864 : ℚ)⟩,
   ⟨14, 8, -10, (671357115 / 268435456 : ℚ)⟩,
   ⟨14, 8, -9, (-5594642625 / 536870912 : ℚ)⟩,
   ⟨14, 8, -8, (705785685 / 33554432 : ℚ)⟩,
   ⟨14, 8, -7, (-25379594185 / 939524096 : ℚ)⟩,
   ⟨14, 8, -6, (22893851431 / 939524096 : ℚ)⟩,
   ⟨14, 8, -5, (-155333048533 / 9663676416 : ℚ)⟩,
   ⟨14, 8, -4, (20059828029343 / 2564900782080 : ℚ)⟩,
   ⟨14, 8, -3, (-1516823295019 / 549621596160 : ℚ)⟩,
   ⟨14, 8, -2, (129460308151 / 192367558656 : ℚ)⟩,
   ⟨14, 8, -1, (-155685007 / 1526726656 : ℚ)⟩,
   ⟨14, 8, 0, (53295 / 7340032 : ℚ)⟩,
   ⟨15, 7, -10, (44757141 / 33554432 : ℚ)⟩,
   ⟨15, 7, -9, (-372976175 / 67108864 : ℚ)⟩,
   ⟨15, 7, -8, (47052379 / 4194304 : ℚ)⟩,
   ⟨15, 7, -7, (-5075918837 / 352321536 : ℚ)⟩,
   ⟨15, 7, -6, (22893851431 / 1761607680 : ℚ)⟩,
   ⟨15, 7, -5, (-155333048533 / 18119393280 : ℚ)⟩,
   ⟨15, 7, -4, (20059828029343 / 4809188966400 : ℚ)⟩,
   ⟨15, 7, -3, (-1516823295019 / 1030540492800 : ℚ)⟩,
   ⟨15, 7, -2, (129460308151 / 360689172480 : ℚ)⟩,
   ⟨15, 7, -1, (-155685007 / 2862612480 : ℚ)⟩,
   ⟨15, 7, 0, (3553 / 917504 : ℚ)⟩,
   ⟨16, 6, -10, (313299987 / 536870912 : ℚ)⟩,
   ⟨16, 6, -9, (-2610833225 / 1073741824 : ℚ)⟩,
   ⟨16, 6, -8, (329366653 / 67108864 : ℚ)⟩,
   ⟨16, 6, -7, (-5075918837 / 805306368 : ℚ)⟩,
   ⟨16, 6, -6, (22893851431 / 4026531840 : ℚ)⟩,
   ⟨16, 6, -5, (-1087331339731 / 289910292480 : ℚ)⟩,
   ⟨16, 6, -4, (20059828029343 / 10992431923200 : ℚ)⟩,
   ⟨16, 6, -3, (-1516823295019 / 2355521126400 : ℚ)⟩,
   ⟨16, 6, -2, (129460308151 / 824432394240 : ℚ)⟩,
   ⟨16, 6, -1, (-155685007 / 6543114240 : ℚ)⟩,
   ⟨16, 6, 0, (3553 / 2097152 : ℚ)⟩,
   ⟨17, 5, -10, (55288233 / 268435456 : ℚ)⟩,
   ⟨17, 5, -9, (-460735275 / 536870912 : ℚ)⟩,
   ⟨17, 5, -8, (58123527 / 33554432 : ℚ)⟩,
   ⟨17, 5, -7, (-298583461 / 134217728 : ℚ)⟩,
   ⟨17, 5, -6, (1346697143 / 671088640 : ℚ)⟩,
   ⟨17, 5, -5, (-63960667043 / 48318382080 : ℚ)⟩,
   ⟨17, 5, -4, (1179989884079 / 1832071987200 : ℚ)⟩,
   ⟨17, 5, -3, (-89224899707 / 392586854400 : ℚ)⟩,
   ⟨17, 5, -2, (129460308151 / 2335891783680 : ℚ)⟩,
   ⟨17, 5, -1, (-155685007 / 18538823680 : ℚ)⟩,
   ⟨17, 5, 0, (627 / 1048576 : ℚ)⟩,
   ⟨18, 4, -10, (30715685 / 536870912 : ℚ)⟩,
   ⟨18, 4, -9, (-767892125 / 3221225472 : ℚ)⟩,
   ⟨18, 4, -8, (96872545 / 201326592 : ℚ)⟩,
   ⟨18, 4, -7, (-1492917305 / 2415919104 : ℚ)⟩,
   ⟨18, 4, -6, (1346697143 / 2415919104 : ℚ)⟩,
   ⟨18, 4, -5, (-63960667043 / 173946175488 : ℚ)⟩,
   ⟨18, 4, -4, (1179989884079 / 6595459153920 : ℚ)⟩,
   ⟨18, 4, -3, (-89224899707 / 1413312675840 : ℚ)⟩,
   ⟨18, 4, -2, (129460308151 / 8409210421248 : ℚ)⟩,
   ⟨18, 4, -1, (-155685007 / 66739765248 : ℚ)⟩,
   ⟨18, 4, 0, (1045 / 6291456 : ℚ)⟩,
   ⟨19, 3, -10, (1616615 / 134217728 : ℚ)⟩,
   ⟨19, 3, -9, (-40415375 / 805306368 : ℚ)⟩,
   ⟨19, 3, -8, (5098555 / 50331648 : ℚ)⟩,
   ⟨19, 3, -7, (-78574595 / 603979776 : ℚ)⟩,
   ⟨19, 3, -6, (70878797 / 603979776 : ℚ)⟩,
   ⟨19, 3, -5, (-3366350897 / 43486543872 : ℚ)⟩,
   ⟨19, 3, -4, (62104730741 / 1648864788480 : ℚ)⟩,
   ⟨19, 3, -3, (-4696047353 / 353328168960 : ℚ)⟩,
   ⟨19, 3, -2, (6813700429 / 2102302605312 : ℚ)⟩,
   ⟨19, 3, -1, (-155685007 / 317013884928 : ℚ)⟩,
   ⟨19, 3, 0, (55 / 1572864 : ℚ)⟩,
   ⟨20, 2, -10, (969969 / 536870912 : ℚ)⟩,
   ⟨20, 2, -9, (-8083075 / 1073741824 : ℚ)⟩,
   ⟨20, 2, -8, (1019711 / 67108864 : ℚ)⟩,
   ⟨20, 2, -7, (-15714919 / 805306368 : ℚ)⟩,
   ⟨20, 2, -6, (70878797 / 4026531840 : ℚ)⟩,
   ⟨20, 2, -5, (-3366350897 / 289910292480 : ℚ)⟩,
   ⟨20, 2, -4, (62104730741 / 10992431923200 : ℚ)⟩,
   ⟨20, 2, -3, (-4696047353 / 2355521126400 : ℚ)⟩,
   ⟨20, 2, -2, (6813700429 / 14015350702080 : ℚ)⟩,
   ⟨20, 2, -1, (-155685007 / 2113425899520 : ℚ)⟩,
   ⟨20, 2, 0, (11 / 2097152 : ℚ)⟩,
   ⟨21, 1, -10, (46189 / 268435456 : ℚ)⟩,
   ⟨21, 1, -9, (-1154725 / 1610612736 : ℚ)⟩,
   ⟨21, 1, -8, (145673 / 100663296 : ℚ)⟩,
   ⟨21, 1, -7, (-15714919 / 8455716864 : ℚ)⟩,
   ⟨21, 1, -6, (70878797 / 42278584320 : ℚ)⟩,
   ⟨21, 1, -5, (-480907271 / 434865438720 : ℚ)⟩,
   ⟨21, 1, -4, (62104730741 / 115420535193600 : ℚ)⟩,
   ⟨21, 1, -3, (-4696047353 / 24732971827200 : ℚ)⟩,
   ⟨21, 1, -2, (6813700429 / 147161182371840 : ℚ)⟩,
   ⟨21, 1, -1, (-155685007 / 22190971944960 : ℚ)⟩,
   ⟨21, 1, 0, (11 / 22020096 : ℚ)⟩,
   ⟨22, 0, -10, (4199 / 536870912 : ℚ)⟩,
   ⟨22, 0, -9, (-104975 / 3221225472 : ℚ)⟩,
   ⟨22, 0, -8, (13243 / 201326592 : ℚ)⟩,
   ⟨22, 0, -7, (-1428629 / 16911433728 : ℚ)⟩,
   ⟨22, 0, -6, (6443527 / 84557168640 : ℚ)⟩,
   ⟨22, 0, -5, (-480907271 / 9567039651840 : ℚ)⟩,
   ⟨22, 0, -4, (62104730741 / 2539251774259200 : ℚ)⟩,
   ⟨22, 0, -3, (-4696047353 / 544125380198400 : ℚ)⟩,
   ⟨22, 0, -2, (6813700429 / 3237546012180480 : ℚ)⟩,
   ⟨22, 0, -1, (-155685007 / 488201382789120 : ℚ)⟩,
   ⟨22, 0, 0, (1 / 44040192 : ℚ)⟩]

def body22_raw : List Term := truncate 24 (rawMul halfPower22 inversePower21)

theorem body22_raw_bound : degreeBound 24 body22_raw = true := by
  decide +kernel

theorem body22_result_bound : degreeBound 24 body22 = true := by
  decide +kernel

theorem body22_degree0 : equalityCheck (degreePart 0 body22_raw) (degreePart 0 body22) = true := by
  decide +kernel

theorem body22_degree1 : equalityCheck (degreePart 1 body22_raw) (degreePart 1 body22) = true := by
  decide +kernel

theorem body22_degree2 : equalityCheck (degreePart 2 body22_raw) (degreePart 2 body22) = true := by
  decide +kernel

theorem body22_degree3 : equalityCheck (degreePart 3 body22_raw) (degreePart 3 body22) = true := by
  decide +kernel

theorem body22_degree4 : equalityCheck (degreePart 4 body22_raw) (degreePart 4 body22) = true := by
  decide +kernel

theorem body22_degree5 : equalityCheck (degreePart 5 body22_raw) (degreePart 5 body22) = true := by
  decide +kernel

theorem body22_degree6 : equalityCheck (degreePart 6 body22_raw) (degreePart 6 body22) = true := by
  decide +kernel

theorem body22_degree7 : equalityCheck (degreePart 7 body22_raw) (degreePart 7 body22) = true := by
  decide +kernel

theorem body22_degree8 : equalityCheck (degreePart 8 body22_raw) (degreePart 8 body22) = true := by
  decide +kernel

theorem body22_degree9 : equalityCheck (degreePart 9 body22_raw) (degreePart 9 body22) = true := by
  decide +kernel

theorem body22_degree10 : equalityCheck (degreePart 10 body22_raw) (degreePart 10 body22) = true := by
  decide +kernel

theorem body22_degree11 : equalityCheck (degreePart 11 body22_raw) (degreePart 11 body22) = true := by
  decide +kernel

theorem body22_degree12 : equalityCheck (degreePart 12 body22_raw) (degreePart 12 body22) = true := by
  decide +kernel

theorem body22_degree13 : equalityCheck (degreePart 13 body22_raw) (degreePart 13 body22) = true := by
  decide +kernel

theorem body22_degree14 : equalityCheck (degreePart 14 body22_raw) (degreePart 14 body22) = true := by
  decide +kernel

theorem body22_degree15 : equalityCheck (degreePart 15 body22_raw) (degreePart 15 body22) = true := by
  decide +kernel

theorem body22_degree16 : equalityCheck (degreePart 16 body22_raw) (degreePart 16 body22) = true := by
  decide +kernel

theorem body22_degree17 : equalityCheck (degreePart 17 body22_raw) (degreePart 17 body22) = true := by
  decide +kernel

theorem body22_degree18 : equalityCheck (degreePart 18 body22_raw) (degreePart 18 body22) = true := by
  decide +kernel

theorem body22_degree19 : equalityCheck (degreePart 19 body22_raw) (degreePart 19 body22) = true := by
  decide +kernel

theorem body22_degree20 : equalityCheck (degreePart 20 body22_raw) (degreePart 20 body22) = true := by
  decide +kernel

theorem body22_degree21 : equalityCheck (degreePart 21 body22_raw) (degreePart 21 body22) = true := by
  decide +kernel

theorem body22_degree22 : equalityCheck (degreePart 22 body22_raw) (degreePart 22 body22) = true := by
  decide +kernel

theorem body22_degree23 : equalityCheck (degreePart 23 body22_raw) (degreePart 23 body22) = true := by
  decide +kernel

theorem body22_degrees (d : ℕ) (hd : d<24) :
    equalityCheck (degreePart d body22_raw) (degreePart d body22) = true := by
  interval_cases d
  · exact body22_degree0
  · exact body22_degree1
  · exact body22_degree2
  · exact body22_degree3
  · exact body22_degree4
  · exact body22_degree5
  · exact body22_degree6
  · exact body22_degree7
  · exact body22_degree8
  · exact body22_degree9
  · exact body22_degree10
  · exact body22_degree11
  · exact body22_degree12
  · exact body22_degree13
  · exact body22_degree14
  · exact body22_degree15
  · exact body22_degree16
  · exact body22_degree17
  · exact body22_degree18
  · exact body22_degree19
  · exact body22_degree20
  · exact body22_degree21
  · exact body22_degree22
  · exact body22_degree23

theorem body22_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 halfPower22 inversePower21) z = eval k body22 z := by
  have he := eval_eq_of_degrees 24 k body22_raw body22 z
    (degreeBound_sound body22_raw_bound) (degreeBound_sound body22_result_bound)
    body22_degrees
  change eval k (normalize body22_raw) z = eval k body22 z
  rw [eval_normalize]
  exact he

def group22_raw : List Term := truncate 24 (rawMul coefficient22 body22)

theorem group22_raw_bound : degreeBound 24 group22_raw = true := by
  decide +kernel

theorem group22_result_bound : degreeBound 24 group22 = true := by
  decide +kernel

theorem group22_degree0 : equalityCheck (degreePart 0 group22_raw) (degreePart 0 group22) = true := by
  decide +kernel

theorem group22_degree1 : equalityCheck (degreePart 1 group22_raw) (degreePart 1 group22) = true := by
  decide +kernel

theorem group22_degree2 : equalityCheck (degreePart 2 group22_raw) (degreePart 2 group22) = true := by
  decide +kernel

theorem group22_degree3 : equalityCheck (degreePart 3 group22_raw) (degreePart 3 group22) = true := by
  decide +kernel

theorem group22_degree4 : equalityCheck (degreePart 4 group22_raw) (degreePart 4 group22) = true := by
  decide +kernel

theorem group22_degree5 : equalityCheck (degreePart 5 group22_raw) (degreePart 5 group22) = true := by
  decide +kernel

theorem group22_degree6 : equalityCheck (degreePart 6 group22_raw) (degreePart 6 group22) = true := by
  decide +kernel

theorem group22_degree7 : equalityCheck (degreePart 7 group22_raw) (degreePart 7 group22) = true := by
  decide +kernel

theorem group22_degree8 : equalityCheck (degreePart 8 group22_raw) (degreePart 8 group22) = true := by
  decide +kernel

theorem group22_degree9 : equalityCheck (degreePart 9 group22_raw) (degreePart 9 group22) = true := by
  decide +kernel

theorem group22_degree10 : equalityCheck (degreePart 10 group22_raw) (degreePart 10 group22) = true := by
  decide +kernel

theorem group22_degree11 : equalityCheck (degreePart 11 group22_raw) (degreePart 11 group22) = true := by
  decide +kernel

theorem group22_degree12 : equalityCheck (degreePart 12 group22_raw) (degreePart 12 group22) = true := by
  decide +kernel

theorem group22_degree13 : equalityCheck (degreePart 13 group22_raw) (degreePart 13 group22) = true := by
  decide +kernel

theorem group22_degree14 : equalityCheck (degreePart 14 group22_raw) (degreePart 14 group22) = true := by
  decide +kernel

theorem group22_degree15 : equalityCheck (degreePart 15 group22_raw) (degreePart 15 group22) = true := by
  decide +kernel

theorem group22_degree16 : equalityCheck (degreePart 16 group22_raw) (degreePart 16 group22) = true := by
  decide +kernel

theorem group22_degree17 : equalityCheck (degreePart 17 group22_raw) (degreePart 17 group22) = true := by
  decide +kernel

theorem group22_degree18 : equalityCheck (degreePart 18 group22_raw) (degreePart 18 group22) = true := by
  decide +kernel

theorem group22_degree19 : equalityCheck (degreePart 19 group22_raw) (degreePart 19 group22) = true := by
  decide +kernel

theorem group22_degree20 : equalityCheck (degreePart 20 group22_raw) (degreePart 20 group22) = true := by
  decide +kernel

theorem group22_degree21 : equalityCheck (degreePart 21 group22_raw) (degreePart 21 group22) = true := by
  decide +kernel

theorem group22_degree22 : equalityCheck (degreePart 22 group22_raw) (degreePart 22 group22) = true := by
  decide +kernel

theorem group22_degree23 : equalityCheck (degreePart 23 group22_raw) (degreePart 23 group22) = true := by
  decide +kernel

theorem group22_degrees (d : ℕ) (hd : d<24) :
    equalityCheck (degreePart d group22_raw) (degreePart d group22) = true := by
  interval_cases d
  · exact group22_degree0
  · exact group22_degree1
  · exact group22_degree2
  · exact group22_degree3
  · exact group22_degree4
  · exact group22_degree5
  · exact group22_degree6
  · exact group22_degree7
  · exact group22_degree8
  · exact group22_degree9
  · exact group22_degree10
  · exact group22_degree11
  · exact group22_degree12
  · exact group22_degree13
  · exact group22_degree14
  · exact group22_degree15
  · exact group22_degree16
  · exact group22_degree17
  · exact group22_degree18
  · exact group22_degree19
  · exact group22_degree20
  · exact group22_degree21
  · exact group22_degree22
  · exact group22_degree23

theorem group22_eval (k : ℂ) (z : ℂ × ℂ) :
    eval k (mulTrunc 24 coefficient22 body22) z = eval k group22 z := by
  have he := eval_eq_of_degrees 24 k group22_raw group22 z
    (degreeBound_sound group22_raw_bound) (degreeBound_sound group22_result_bound)
    group22_degrees
  change eval k (normalize group22_raw) z = eval k group22 z
  rw [eval_normalize]
  exact he

theorem coefficient22_approximates (k : ℂ) :
    Approximates 24 k (fun _ => eval k coefficient22 (0:ℂ × ℂ)) coefficient22 := by
  convert Approximates.exactPolynomial 24 k coefficient22 using 1
  funext z
  simp [coefficient22,eval,evalTerm]

theorem evalContact_group22 (k s e : ℂ) :
    evalContact k phiGroup22 s e = eval k coefficient22 (0:ℂ × ℂ)*(s^22*(e⁻¹)^21) := by
  norm_num [phiGroup22,coefficient22,evalContact,evalContactTerm,eval,evalTerm]
  <;> ring

theorem group22_approximates {k : ℂ} (hk : k ≠ 0) (hklog : k = (Real.log 2:ℂ)) :
    Approximates 24 k (fun z => evalContact k phiGroup22 (halfSum z) (meanFunction z)) group22 := by
  have hb := ((halfPower22_approximates hk).mul hk (inversePower21_approximates hk hklog)).replacePolynomial
    (body22_eval k)
  have hh := ((coefficient22_approximates k).mul hk hb).replacePolynomial
    (group22_eval k)
  simpa only [evalContact_group22] using hh

end GeneralCK.Reflection.SmallBiasContactDegrees

end


