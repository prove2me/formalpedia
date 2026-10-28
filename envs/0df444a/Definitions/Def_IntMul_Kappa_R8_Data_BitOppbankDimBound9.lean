-- Prove2me | Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankDimBound9
-- name    : IntMul_Kappa_R8_Data_BitOppbankDimBound9
-- status  : Definition
-- author  : @Ethan Cheung Wang
-- created : 2026-10-28T18:02:28.858279+00:00
-- url     : https://prove2.me/theorems/a9e62e71-3019-4527-bffc-d817fe219559
-- title:
--   Densified dimF $\le 22$ pack 9 ($[45000,50000)$)
-- statement:
--   Pack 9 of the densified dimension-field bound.
--
--   For every densified node index $n$ with $45000\le n<50000$, the 5-bit field $\mathrm{dimF}(n)$ extracted from $\mathrm{DIMT}$ satisfies
--   $$1\le \mathrm{dimF}(n)\le 22.$$
--   Proved by `decide` on successive `Fin 50` windows (no `native_decide`).
-- source:
--   R8 BitNB densified DIMT field bound; Fin-window decide packs

-- DimBound pack 9: dimF bounds on n ∈ [45000, 50000)

import Definitions.Def_IntMul_Kappa_R6_Defs4
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankPnd
import Definitions.Def_IntMul_Kappa_R8_Data_BitOppbankSupG
import Mathlib

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

open IntMul.Kappa.R8.Bit.Oppbank.Pnd
open IntMul.Kappa.R8.Bit.Oppbank.ChkBitArg
open IntMul.Kappa.R8.Bit.Oppbank.SupG

namespace IntMul.Kappa.R8.Bit.Oppbank.DimBound9

private theorem le_w900 : ∀ n : Fin 50, dimF (n.val + 45000) ≤ 22 := by decide
private theorem pos_w900 : ∀ n : Fin 50, 0 < dimF (n.val + 45000) := by decide
private theorem le_w901 : ∀ n : Fin 50, dimF (n.val + 45050) ≤ 22 := by decide
private theorem pos_w901 : ∀ n : Fin 50, 0 < dimF (n.val + 45050) := by decide
private theorem le_w902 : ∀ n : Fin 50, dimF (n.val + 45100) ≤ 22 := by decide
private theorem pos_w902 : ∀ n : Fin 50, 0 < dimF (n.val + 45100) := by decide
private theorem le_w903 : ∀ n : Fin 50, dimF (n.val + 45150) ≤ 22 := by decide
private theorem pos_w903 : ∀ n : Fin 50, 0 < dimF (n.val + 45150) := by decide
private theorem le_w904 : ∀ n : Fin 50, dimF (n.val + 45200) ≤ 22 := by decide
private theorem pos_w904 : ∀ n : Fin 50, 0 < dimF (n.val + 45200) := by decide
private theorem le_w905 : ∀ n : Fin 50, dimF (n.val + 45250) ≤ 22 := by decide
private theorem pos_w905 : ∀ n : Fin 50, 0 < dimF (n.val + 45250) := by decide
private theorem le_w906 : ∀ n : Fin 50, dimF (n.val + 45300) ≤ 22 := by decide
private theorem pos_w906 : ∀ n : Fin 50, 0 < dimF (n.val + 45300) := by decide
private theorem le_w907 : ∀ n : Fin 50, dimF (n.val + 45350) ≤ 22 := by decide
private theorem pos_w907 : ∀ n : Fin 50, 0 < dimF (n.val + 45350) := by decide
private theorem le_w908 : ∀ n : Fin 50, dimF (n.val + 45400) ≤ 22 := by decide
private theorem pos_w908 : ∀ n : Fin 50, 0 < dimF (n.val + 45400) := by decide
private theorem le_w909 : ∀ n : Fin 50, dimF (n.val + 45450) ≤ 22 := by decide
private theorem pos_w909 : ∀ n : Fin 50, 0 < dimF (n.val + 45450) := by decide
private theorem le_w910 : ∀ n : Fin 50, dimF (n.val + 45500) ≤ 22 := by decide
private theorem pos_w910 : ∀ n : Fin 50, 0 < dimF (n.val + 45500) := by decide
private theorem le_w911 : ∀ n : Fin 50, dimF (n.val + 45550) ≤ 22 := by decide
private theorem pos_w911 : ∀ n : Fin 50, 0 < dimF (n.val + 45550) := by decide
private theorem le_w912 : ∀ n : Fin 50, dimF (n.val + 45600) ≤ 22 := by decide
private theorem pos_w912 : ∀ n : Fin 50, 0 < dimF (n.val + 45600) := by decide
private theorem le_w913 : ∀ n : Fin 50, dimF (n.val + 45650) ≤ 22 := by decide
private theorem pos_w913 : ∀ n : Fin 50, 0 < dimF (n.val + 45650) := by decide
private theorem le_w914 : ∀ n : Fin 50, dimF (n.val + 45700) ≤ 22 := by decide
private theorem pos_w914 : ∀ n : Fin 50, 0 < dimF (n.val + 45700) := by decide
private theorem le_w915 : ∀ n : Fin 50, dimF (n.val + 45750) ≤ 22 := by decide
private theorem pos_w915 : ∀ n : Fin 50, 0 < dimF (n.val + 45750) := by decide
private theorem le_w916 : ∀ n : Fin 50, dimF (n.val + 45800) ≤ 22 := by decide
private theorem pos_w916 : ∀ n : Fin 50, 0 < dimF (n.val + 45800) := by decide
private theorem le_w917 : ∀ n : Fin 50, dimF (n.val + 45850) ≤ 22 := by decide
private theorem pos_w917 : ∀ n : Fin 50, 0 < dimF (n.val + 45850) := by decide
private theorem le_w918 : ∀ n : Fin 50, dimF (n.val + 45900) ≤ 22 := by decide
private theorem pos_w918 : ∀ n : Fin 50, 0 < dimF (n.val + 45900) := by decide
private theorem le_w919 : ∀ n : Fin 50, dimF (n.val + 45950) ≤ 22 := by decide
private theorem pos_w919 : ∀ n : Fin 50, 0 < dimF (n.val + 45950) := by decide
private theorem le_w920 : ∀ n : Fin 50, dimF (n.val + 46000) ≤ 22 := by decide
private theorem pos_w920 : ∀ n : Fin 50, 0 < dimF (n.val + 46000) := by decide
private theorem le_w921 : ∀ n : Fin 50, dimF (n.val + 46050) ≤ 22 := by decide
private theorem pos_w921 : ∀ n : Fin 50, 0 < dimF (n.val + 46050) := by decide
private theorem le_w922 : ∀ n : Fin 50, dimF (n.val + 46100) ≤ 22 := by decide
private theorem pos_w922 : ∀ n : Fin 50, 0 < dimF (n.val + 46100) := by decide
private theorem le_w923 : ∀ n : Fin 50, dimF (n.val + 46150) ≤ 22 := by decide
private theorem pos_w923 : ∀ n : Fin 50, 0 < dimF (n.val + 46150) := by decide
private theorem le_w924 : ∀ n : Fin 50, dimF (n.val + 46200) ≤ 22 := by decide
private theorem pos_w924 : ∀ n : Fin 50, 0 < dimF (n.val + 46200) := by decide
private theorem le_w925 : ∀ n : Fin 50, dimF (n.val + 46250) ≤ 22 := by decide
private theorem pos_w925 : ∀ n : Fin 50, 0 < dimF (n.val + 46250) := by decide
private theorem le_w926 : ∀ n : Fin 50, dimF (n.val + 46300) ≤ 22 := by decide
private theorem pos_w926 : ∀ n : Fin 50, 0 < dimF (n.val + 46300) := by decide
private theorem le_w927 : ∀ n : Fin 50, dimF (n.val + 46350) ≤ 22 := by decide
private theorem pos_w927 : ∀ n : Fin 50, 0 < dimF (n.val + 46350) := by decide
private theorem le_w928 : ∀ n : Fin 50, dimF (n.val + 46400) ≤ 22 := by decide
private theorem pos_w928 : ∀ n : Fin 50, 0 < dimF (n.val + 46400) := by decide
private theorem le_w929 : ∀ n : Fin 50, dimF (n.val + 46450) ≤ 22 := by decide
private theorem pos_w929 : ∀ n : Fin 50, 0 < dimF (n.val + 46450) := by decide
private theorem le_w930 : ∀ n : Fin 50, dimF (n.val + 46500) ≤ 22 := by decide
private theorem pos_w930 : ∀ n : Fin 50, 0 < dimF (n.val + 46500) := by decide
private theorem le_w931 : ∀ n : Fin 50, dimF (n.val + 46550) ≤ 22 := by decide
private theorem pos_w931 : ∀ n : Fin 50, 0 < dimF (n.val + 46550) := by decide
private theorem le_w932 : ∀ n : Fin 50, dimF (n.val + 46600) ≤ 22 := by decide
private theorem pos_w932 : ∀ n : Fin 50, 0 < dimF (n.val + 46600) := by decide
private theorem le_w933 : ∀ n : Fin 50, dimF (n.val + 46650) ≤ 22 := by decide
private theorem pos_w933 : ∀ n : Fin 50, 0 < dimF (n.val + 46650) := by decide
private theorem le_w934 : ∀ n : Fin 50, dimF (n.val + 46700) ≤ 22 := by decide
private theorem pos_w934 : ∀ n : Fin 50, 0 < dimF (n.val + 46700) := by decide
private theorem le_w935 : ∀ n : Fin 50, dimF (n.val + 46750) ≤ 22 := by decide
private theorem pos_w935 : ∀ n : Fin 50, 0 < dimF (n.val + 46750) := by decide
private theorem le_w936 : ∀ n : Fin 50, dimF (n.val + 46800) ≤ 22 := by decide
private theorem pos_w936 : ∀ n : Fin 50, 0 < dimF (n.val + 46800) := by decide
private theorem le_w937 : ∀ n : Fin 50, dimF (n.val + 46850) ≤ 22 := by decide
private theorem pos_w937 : ∀ n : Fin 50, 0 < dimF (n.val + 46850) := by decide
private theorem le_w938 : ∀ n : Fin 50, dimF (n.val + 46900) ≤ 22 := by decide
private theorem pos_w938 : ∀ n : Fin 50, 0 < dimF (n.val + 46900) := by decide
private theorem le_w939 : ∀ n : Fin 50, dimF (n.val + 46950) ≤ 22 := by decide
private theorem pos_w939 : ∀ n : Fin 50, 0 < dimF (n.val + 46950) := by decide
private theorem le_w940 : ∀ n : Fin 50, dimF (n.val + 47000) ≤ 22 := by decide
private theorem pos_w940 : ∀ n : Fin 50, 0 < dimF (n.val + 47000) := by decide
private theorem le_w941 : ∀ n : Fin 50, dimF (n.val + 47050) ≤ 22 := by decide
private theorem pos_w941 : ∀ n : Fin 50, 0 < dimF (n.val + 47050) := by decide
private theorem le_w942 : ∀ n : Fin 50, dimF (n.val + 47100) ≤ 22 := by decide
private theorem pos_w942 : ∀ n : Fin 50, 0 < dimF (n.val + 47100) := by decide
private theorem le_w943 : ∀ n : Fin 50, dimF (n.val + 47150) ≤ 22 := by decide
private theorem pos_w943 : ∀ n : Fin 50, 0 < dimF (n.val + 47150) := by decide
private theorem le_w944 : ∀ n : Fin 50, dimF (n.val + 47200) ≤ 22 := by decide
private theorem pos_w944 : ∀ n : Fin 50, 0 < dimF (n.val + 47200) := by decide
private theorem le_w945 : ∀ n : Fin 50, dimF (n.val + 47250) ≤ 22 := by decide
private theorem pos_w945 : ∀ n : Fin 50, 0 < dimF (n.val + 47250) := by decide
private theorem le_w946 : ∀ n : Fin 50, dimF (n.val + 47300) ≤ 22 := by decide
private theorem pos_w946 : ∀ n : Fin 50, 0 < dimF (n.val + 47300) := by decide
private theorem le_w947 : ∀ n : Fin 50, dimF (n.val + 47350) ≤ 22 := by decide
private theorem pos_w947 : ∀ n : Fin 50, 0 < dimF (n.val + 47350) := by decide
private theorem le_w948 : ∀ n : Fin 50, dimF (n.val + 47400) ≤ 22 := by decide
private theorem pos_w948 : ∀ n : Fin 50, 0 < dimF (n.val + 47400) := by decide
private theorem le_w949 : ∀ n : Fin 50, dimF (n.val + 47450) ≤ 22 := by decide
private theorem pos_w949 : ∀ n : Fin 50, 0 < dimF (n.val + 47450) := by decide
private theorem le_w950 : ∀ n : Fin 50, dimF (n.val + 47500) ≤ 22 := by decide
private theorem pos_w950 : ∀ n : Fin 50, 0 < dimF (n.val + 47500) := by decide
private theorem le_w951 : ∀ n : Fin 50, dimF (n.val + 47550) ≤ 22 := by decide
private theorem pos_w951 : ∀ n : Fin 50, 0 < dimF (n.val + 47550) := by decide
private theorem le_w952 : ∀ n : Fin 50, dimF (n.val + 47600) ≤ 22 := by decide
private theorem pos_w952 : ∀ n : Fin 50, 0 < dimF (n.val + 47600) := by decide
private theorem le_w953 : ∀ n : Fin 50, dimF (n.val + 47650) ≤ 22 := by decide
private theorem pos_w953 : ∀ n : Fin 50, 0 < dimF (n.val + 47650) := by decide
private theorem le_w954 : ∀ n : Fin 50, dimF (n.val + 47700) ≤ 22 := by decide
private theorem pos_w954 : ∀ n : Fin 50, 0 < dimF (n.val + 47700) := by decide
private theorem le_w955 : ∀ n : Fin 50, dimF (n.val + 47750) ≤ 22 := by decide
private theorem pos_w955 : ∀ n : Fin 50, 0 < dimF (n.val + 47750) := by decide
private theorem le_w956 : ∀ n : Fin 50, dimF (n.val + 47800) ≤ 22 := by decide
private theorem pos_w956 : ∀ n : Fin 50, 0 < dimF (n.val + 47800) := by decide
private theorem le_w957 : ∀ n : Fin 50, dimF (n.val + 47850) ≤ 22 := by decide
private theorem pos_w957 : ∀ n : Fin 50, 0 < dimF (n.val + 47850) := by decide
private theorem le_w958 : ∀ n : Fin 50, dimF (n.val + 47900) ≤ 22 := by decide
private theorem pos_w958 : ∀ n : Fin 50, 0 < dimF (n.val + 47900) := by decide
private theorem le_w959 : ∀ n : Fin 50, dimF (n.val + 47950) ≤ 22 := by decide
private theorem pos_w959 : ∀ n : Fin 50, 0 < dimF (n.val + 47950) := by decide
private theorem le_w960 : ∀ n : Fin 50, dimF (n.val + 48000) ≤ 22 := by decide
private theorem pos_w960 : ∀ n : Fin 50, 0 < dimF (n.val + 48000) := by decide
private theorem le_w961 : ∀ n : Fin 50, dimF (n.val + 48050) ≤ 22 := by decide
private theorem pos_w961 : ∀ n : Fin 50, 0 < dimF (n.val + 48050) := by decide
private theorem le_w962 : ∀ n : Fin 50, dimF (n.val + 48100) ≤ 22 := by decide
private theorem pos_w962 : ∀ n : Fin 50, 0 < dimF (n.val + 48100) := by decide
private theorem le_w963 : ∀ n : Fin 50, dimF (n.val + 48150) ≤ 22 := by decide
private theorem pos_w963 : ∀ n : Fin 50, 0 < dimF (n.val + 48150) := by decide
private theorem le_w964 : ∀ n : Fin 50, dimF (n.val + 48200) ≤ 22 := by decide
private theorem pos_w964 : ∀ n : Fin 50, 0 < dimF (n.val + 48200) := by decide
private theorem le_w965 : ∀ n : Fin 50, dimF (n.val + 48250) ≤ 22 := by decide
private theorem pos_w965 : ∀ n : Fin 50, 0 < dimF (n.val + 48250) := by decide
private theorem le_w966 : ∀ n : Fin 50, dimF (n.val + 48300) ≤ 22 := by decide
private theorem pos_w966 : ∀ n : Fin 50, 0 < dimF (n.val + 48300) := by decide
private theorem le_w967 : ∀ n : Fin 50, dimF (n.val + 48350) ≤ 22 := by decide
private theorem pos_w967 : ∀ n : Fin 50, 0 < dimF (n.val + 48350) := by decide
private theorem le_w968 : ∀ n : Fin 50, dimF (n.val + 48400) ≤ 22 := by decide
private theorem pos_w968 : ∀ n : Fin 50, 0 < dimF (n.val + 48400) := by decide
private theorem le_w969 : ∀ n : Fin 50, dimF (n.val + 48450) ≤ 22 := by decide
private theorem pos_w969 : ∀ n : Fin 50, 0 < dimF (n.val + 48450) := by decide
private theorem le_w970 : ∀ n : Fin 50, dimF (n.val + 48500) ≤ 22 := by decide
private theorem pos_w970 : ∀ n : Fin 50, 0 < dimF (n.val + 48500) := by decide
private theorem le_w971 : ∀ n : Fin 50, dimF (n.val + 48550) ≤ 22 := by decide
private theorem pos_w971 : ∀ n : Fin 50, 0 < dimF (n.val + 48550) := by decide
private theorem le_w972 : ∀ n : Fin 50, dimF (n.val + 48600) ≤ 22 := by decide
private theorem pos_w972 : ∀ n : Fin 50, 0 < dimF (n.val + 48600) := by decide
private theorem le_w973 : ∀ n : Fin 50, dimF (n.val + 48650) ≤ 22 := by decide
private theorem pos_w973 : ∀ n : Fin 50, 0 < dimF (n.val + 48650) := by decide
private theorem le_w974 : ∀ n : Fin 50, dimF (n.val + 48700) ≤ 22 := by decide
private theorem pos_w974 : ∀ n : Fin 50, 0 < dimF (n.val + 48700) := by decide
private theorem le_w975 : ∀ n : Fin 50, dimF (n.val + 48750) ≤ 22 := by decide
private theorem pos_w975 : ∀ n : Fin 50, 0 < dimF (n.val + 48750) := by decide
private theorem le_w976 : ∀ n : Fin 50, dimF (n.val + 48800) ≤ 22 := by decide
private theorem pos_w976 : ∀ n : Fin 50, 0 < dimF (n.val + 48800) := by decide
private theorem le_w977 : ∀ n : Fin 50, dimF (n.val + 48850) ≤ 22 := by decide
private theorem pos_w977 : ∀ n : Fin 50, 0 < dimF (n.val + 48850) := by decide
private theorem le_w978 : ∀ n : Fin 50, dimF (n.val + 48900) ≤ 22 := by decide
private theorem pos_w978 : ∀ n : Fin 50, 0 < dimF (n.val + 48900) := by decide
private theorem le_w979 : ∀ n : Fin 50, dimF (n.val + 48950) ≤ 22 := by decide
private theorem pos_w979 : ∀ n : Fin 50, 0 < dimF (n.val + 48950) := by decide
private theorem le_w980 : ∀ n : Fin 50, dimF (n.val + 49000) ≤ 22 := by decide
private theorem pos_w980 : ∀ n : Fin 50, 0 < dimF (n.val + 49000) := by decide
private theorem le_w981 : ∀ n : Fin 50, dimF (n.val + 49050) ≤ 22 := by decide
private theorem pos_w981 : ∀ n : Fin 50, 0 < dimF (n.val + 49050) := by decide
private theorem le_w982 : ∀ n : Fin 50, dimF (n.val + 49100) ≤ 22 := by decide
private theorem pos_w982 : ∀ n : Fin 50, 0 < dimF (n.val + 49100) := by decide
private theorem le_w983 : ∀ n : Fin 50, dimF (n.val + 49150) ≤ 22 := by decide
private theorem pos_w983 : ∀ n : Fin 50, 0 < dimF (n.val + 49150) := by decide
private theorem le_w984 : ∀ n : Fin 50, dimF (n.val + 49200) ≤ 22 := by decide
private theorem pos_w984 : ∀ n : Fin 50, 0 < dimF (n.val + 49200) := by decide
private theorem le_w985 : ∀ n : Fin 50, dimF (n.val + 49250) ≤ 22 := by decide
private theorem pos_w985 : ∀ n : Fin 50, 0 < dimF (n.val + 49250) := by decide
private theorem le_w986 : ∀ n : Fin 50, dimF (n.val + 49300) ≤ 22 := by decide
private theorem pos_w986 : ∀ n : Fin 50, 0 < dimF (n.val + 49300) := by decide
private theorem le_w987 : ∀ n : Fin 50, dimF (n.val + 49350) ≤ 22 := by decide
private theorem pos_w987 : ∀ n : Fin 50, 0 < dimF (n.val + 49350) := by decide
private theorem le_w988 : ∀ n : Fin 50, dimF (n.val + 49400) ≤ 22 := by decide
private theorem pos_w988 : ∀ n : Fin 50, 0 < dimF (n.val + 49400) := by decide
private theorem le_w989 : ∀ n : Fin 50, dimF (n.val + 49450) ≤ 22 := by decide
private theorem pos_w989 : ∀ n : Fin 50, 0 < dimF (n.val + 49450) := by decide
private theorem le_w990 : ∀ n : Fin 50, dimF (n.val + 49500) ≤ 22 := by decide
private theorem pos_w990 : ∀ n : Fin 50, 0 < dimF (n.val + 49500) := by decide
private theorem le_w991 : ∀ n : Fin 50, dimF (n.val + 49550) ≤ 22 := by decide
private theorem pos_w991 : ∀ n : Fin 50, 0 < dimF (n.val + 49550) := by decide
private theorem le_w992 : ∀ n : Fin 50, dimF (n.val + 49600) ≤ 22 := by decide
private theorem pos_w992 : ∀ n : Fin 50, 0 < dimF (n.val + 49600) := by decide
private theorem le_w993 : ∀ n : Fin 50, dimF (n.val + 49650) ≤ 22 := by decide
private theorem pos_w993 : ∀ n : Fin 50, 0 < dimF (n.val + 49650) := by decide
private theorem le_w994 : ∀ n : Fin 50, dimF (n.val + 49700) ≤ 22 := by decide
private theorem pos_w994 : ∀ n : Fin 50, 0 < dimF (n.val + 49700) := by decide
private theorem le_w995 : ∀ n : Fin 50, dimF (n.val + 49750) ≤ 22 := by decide
private theorem pos_w995 : ∀ n : Fin 50, 0 < dimF (n.val + 49750) := by decide
private theorem le_w996 : ∀ n : Fin 50, dimF (n.val + 49800) ≤ 22 := by decide
private theorem pos_w996 : ∀ n : Fin 50, 0 < dimF (n.val + 49800) := by decide
private theorem le_w997 : ∀ n : Fin 50, dimF (n.val + 49850) ≤ 22 := by decide
private theorem pos_w997 : ∀ n : Fin 50, 0 < dimF (n.val + 49850) := by decide
private theorem le_w998 : ∀ n : Fin 50, dimF (n.val + 49900) ≤ 22 := by decide
private theorem pos_w998 : ∀ n : Fin 50, 0 < dimF (n.val + 49900) := by decide
private theorem le_w999 : ∀ n : Fin 50, dimF (n.val + 49950) ≤ 22 := by decide
private theorem pos_w999 : ∀ n : Fin 50, 0 < dimF (n.val + 49950) := by decide

theorem dimF_le_22_range : ∀ n, 45000 ≤ n → n < 50000 → dimF n ≤ 22 := by
  intro n hlo hhi
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact le_w900 ⟨n - 45000, hr⟩
  · by_cases h1 : n < 45100
    · have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact le_w901 ⟨n - 45050, hr⟩
    · by_cases h2 : n < 45150
      · have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact le_w902 ⟨n - 45100, hr⟩
      · by_cases h3 : n < 45200
        · have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact le_w903 ⟨n - 45150, hr⟩
        · by_cases h4 : n < 45250
          · have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact le_w904 ⟨n - 45200, hr⟩
          · by_cases h5 : n < 45300
            · have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact le_w905 ⟨n - 45250, hr⟩
            · by_cases h6 : n < 45350
              · have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact le_w906 ⟨n - 45300, hr⟩
              · by_cases h7 : n < 45400
                · have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact le_w907 ⟨n - 45350, hr⟩
                · by_cases h8 : n < 45450
                  · have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact le_w908 ⟨n - 45400, hr⟩
                  · by_cases h9 : n < 45500
                    · have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact le_w909 ⟨n - 45450, hr⟩
                    · by_cases h10 : n < 45550
                      · have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact le_w910 ⟨n - 45500, hr⟩
                      · by_cases h11 : n < 45600
                        · have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact le_w911 ⟨n - 45550, hr⟩
                        · by_cases h12 : n < 45650
                          · have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact le_w912 ⟨n - 45600, hr⟩
                          · by_cases h13 : n < 45700
                            · have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact le_w913 ⟨n - 45650, hr⟩
                            · by_cases h14 : n < 45750
                              · have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact le_w914 ⟨n - 45700, hr⟩
                              · by_cases h15 : n < 45800
                                · have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact le_w915 ⟨n - 45750, hr⟩
                                · by_cases h16 : n < 45850
                                  · have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact le_w916 ⟨n - 45800, hr⟩
                                  · by_cases h17 : n < 45900
                                    · have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact le_w917 ⟨n - 45850, hr⟩
                                    · by_cases h18 : n < 45950
                                      · have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact le_w918 ⟨n - 45900, hr⟩
                                      · by_cases h19 : n < 46000
                                        · have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact le_w919 ⟨n - 45950, hr⟩
                                        · by_cases h20 : n < 46050
                                          · have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact le_w920 ⟨n - 46000, hr⟩
                                          · by_cases h21 : n < 46100
                                            · have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact le_w921 ⟨n - 46050, hr⟩
                                            · by_cases h22 : n < 46150
                                              · have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact le_w922 ⟨n - 46100, hr⟩
                                              · by_cases h23 : n < 46200
                                                · have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact le_w923 ⟨n - 46150, hr⟩
                                                · by_cases h24 : n < 46250
                                                  · have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact le_w924 ⟨n - 46200, hr⟩
                                                  · by_cases h25 : n < 46300
                                                    · have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact le_w925 ⟨n - 46250, hr⟩
                                                    · by_cases h26 : n < 46350
                                                      · have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact le_w926 ⟨n - 46300, hr⟩
                                                      · by_cases h27 : n < 46400
                                                        · have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact le_w927 ⟨n - 46350, hr⟩
                                                        · by_cases h28 : n < 46450
                                                          · have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact le_w928 ⟨n - 46400, hr⟩
                                                          · by_cases h29 : n < 46500
                                                            · have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact le_w929 ⟨n - 46450, hr⟩
                                                            · by_cases h30 : n < 46550
                                                              · have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact le_w930 ⟨n - 46500, hr⟩
                                                              · by_cases h31 : n < 46600
                                                                · have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact le_w931 ⟨n - 46550, hr⟩
                                                                · by_cases h32 : n < 46650
                                                                  · have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact le_w932 ⟨n - 46600, hr⟩
                                                                  · by_cases h33 : n < 46700
                                                                    · have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact le_w933 ⟨n - 46650, hr⟩
                                                                    · by_cases h34 : n < 46750
                                                                      · have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact le_w934 ⟨n - 46700, hr⟩
                                                                      · by_cases h35 : n < 46800
                                                                        · have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact le_w935 ⟨n - 46750, hr⟩
                                                                        · by_cases h36 : n < 46850
                                                                          · have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact le_w936 ⟨n - 46800, hr⟩
                                                                          · by_cases h37 : n < 46900
                                                                            · have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact le_w937 ⟨n - 46850, hr⟩
                                                                            · by_cases h38 : n < 46950
                                                                              · have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact le_w938 ⟨n - 46900, hr⟩
                                                                              · by_cases h39 : n < 47000
                                                                                · have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact le_w939 ⟨n - 46950, hr⟩
                                                                                · by_cases h40 : n < 47050
                                                                                  · have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact le_w940 ⟨n - 47000, hr⟩
                                                                                  · by_cases h41 : n < 47100
                                                                                    · have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact le_w941 ⟨n - 47050, hr⟩
                                                                                    · by_cases h42 : n < 47150
                                                                                      · have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact le_w942 ⟨n - 47100, hr⟩
                                                                                      · by_cases h43 : n < 47200
                                                                                        · have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact le_w943 ⟨n - 47150, hr⟩
                                                                                        · by_cases h44 : n < 47250
                                                                                          · have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact le_w944 ⟨n - 47200, hr⟩
                                                                                          · by_cases h45 : n < 47300
                                                                                            · have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact le_w945 ⟨n - 47250, hr⟩
                                                                                            · by_cases h46 : n < 47350
                                                                                              · have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact le_w946 ⟨n - 47300, hr⟩
                                                                                              · by_cases h47 : n < 47400
                                                                                                · have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact le_w947 ⟨n - 47350, hr⟩
                                                                                                · by_cases h48 : n < 47450
                                                                                                  · have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact le_w948 ⟨n - 47400, hr⟩
                                                                                                  · by_cases h49 : n < 47500
                                                                                                    · have hr : n - 47450 < 50 := by omega
                                                                                                      have heq : n = (n - 47450) + 47450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact le_w949 ⟨n - 47450, hr⟩
                                                                                                    · by_cases h50 : n < 47550
                                                                                                      · have hr : n - 47500 < 50 := by omega
                                                                                                        have heq : n = (n - 47500) + 47500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact le_w950 ⟨n - 47500, hr⟩
                                                                                                      · by_cases h51 : n < 47600
                                                                                                        · have hr : n - 47550 < 50 := by omega
                                                                                                          have heq : n = (n - 47550) + 47550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact le_w951 ⟨n - 47550, hr⟩
                                                                                                        · by_cases h52 : n < 47650
                                                                                                          · have hr : n - 47600 < 50 := by omega
                                                                                                            have heq : n = (n - 47600) + 47600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact le_w952 ⟨n - 47600, hr⟩
                                                                                                          · by_cases h53 : n < 47700
                                                                                                            · have hr : n - 47650 < 50 := by omega
                                                                                                              have heq : n = (n - 47650) + 47650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact le_w953 ⟨n - 47650, hr⟩
                                                                                                            · by_cases h54 : n < 47750
                                                                                                              · have hr : n - 47700 < 50 := by omega
                                                                                                                have heq : n = (n - 47700) + 47700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact le_w954 ⟨n - 47700, hr⟩
                                                                                                              · by_cases h55 : n < 47800
                                                                                                                · have hr : n - 47750 < 50 := by omega
                                                                                                                  have heq : n = (n - 47750) + 47750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact le_w955 ⟨n - 47750, hr⟩
                                                                                                                · by_cases h56 : n < 47850
                                                                                                                  · have hr : n - 47800 < 50 := by omega
                                                                                                                    have heq : n = (n - 47800) + 47800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact le_w956 ⟨n - 47800, hr⟩
                                                                                                                  · by_cases h57 : n < 47900
                                                                                                                    · have hr : n - 47850 < 50 := by omega
                                                                                                                      have heq : n = (n - 47850) + 47850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact le_w957 ⟨n - 47850, hr⟩
                                                                                                                    · by_cases h58 : n < 47950
                                                                                                                      · have hr : n - 47900 < 50 := by omega
                                                                                                                        have heq : n = (n - 47900) + 47900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact le_w958 ⟨n - 47900, hr⟩
                                                                                                                      · by_cases h59 : n < 48000
                                                                                                                        · have hr : n - 47950 < 50 := by omega
                                                                                                                          have heq : n = (n - 47950) + 47950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact le_w959 ⟨n - 47950, hr⟩
                                                                                                                        · by_cases h60 : n < 48050
                                                                                                                          · have hr : n - 48000 < 50 := by omega
                                                                                                                            have heq : n = (n - 48000) + 48000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact le_w960 ⟨n - 48000, hr⟩
                                                                                                                          · by_cases h61 : n < 48100
                                                                                                                            · have hr : n - 48050 < 50 := by omega
                                                                                                                              have heq : n = (n - 48050) + 48050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact le_w961 ⟨n - 48050, hr⟩
                                                                                                                            · by_cases h62 : n < 48150
                                                                                                                              · have hr : n - 48100 < 50 := by omega
                                                                                                                                have heq : n = (n - 48100) + 48100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact le_w962 ⟨n - 48100, hr⟩
                                                                                                                              · by_cases h63 : n < 48200
                                                                                                                                · have hr : n - 48150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 48150) + 48150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact le_w963 ⟨n - 48150, hr⟩
                                                                                                                                · by_cases h64 : n < 48250
                                                                                                                                  · have hr : n - 48200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 48200) + 48200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact le_w964 ⟨n - 48200, hr⟩
                                                                                                                                  · by_cases h65 : n < 48300
                                                                                                                                    · have hr : n - 48250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 48250) + 48250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact le_w965 ⟨n - 48250, hr⟩
                                                                                                                                    · by_cases h66 : n < 48350
                                                                                                                                      · have hr : n - 48300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 48300) + 48300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact le_w966 ⟨n - 48300, hr⟩
                                                                                                                                      · by_cases h67 : n < 48400
                                                                                                                                        · have hr : n - 48350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 48350) + 48350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact le_w967 ⟨n - 48350, hr⟩
                                                                                                                                        · by_cases h68 : n < 48450
                                                                                                                                          · have hr : n - 48400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 48400) + 48400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact le_w968 ⟨n - 48400, hr⟩
                                                                                                                                          · by_cases h69 : n < 48500
                                                                                                                                            · have hr : n - 48450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 48450) + 48450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact le_w969 ⟨n - 48450, hr⟩
                                                                                                                                            · by_cases h70 : n < 48550
                                                                                                                                              · have hr : n - 48500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 48500) + 48500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact le_w970 ⟨n - 48500, hr⟩
                                                                                                                                              · by_cases h71 : n < 48600
                                                                                                                                                · have hr : n - 48550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 48550) + 48550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact le_w971 ⟨n - 48550, hr⟩
                                                                                                                                                · by_cases h72 : n < 48650
                                                                                                                                                  · have hr : n - 48600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 48600) + 48600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact le_w972 ⟨n - 48600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 48700
                                                                                                                                                    · have hr : n - 48650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 48650) + 48650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact le_w973 ⟨n - 48650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 48750
                                                                                                                                                      · have hr : n - 48700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 48700) + 48700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact le_w974 ⟨n - 48700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 48800
                                                                                                                                                        · have hr : n - 48750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 48750) + 48750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact le_w975 ⟨n - 48750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 48850
                                                                                                                                                          · have hr : n - 48800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 48800) + 48800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact le_w976 ⟨n - 48800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 48900
                                                                                                                                                            · have hr : n - 48850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 48850) + 48850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact le_w977 ⟨n - 48850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 48950
                                                                                                                                                              · have hr : n - 48900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 48900) + 48900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact le_w978 ⟨n - 48900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 49000
                                                                                                                                                                · have hr : n - 48950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 48950) + 48950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact le_w979 ⟨n - 48950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 49050
                                                                                                                                                                  · have hr : n - 49000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 49000) + 49000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact le_w980 ⟨n - 49000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 49100
                                                                                                                                                                    · have hr : n - 49050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 49050) + 49050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact le_w981 ⟨n - 49050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 49150
                                                                                                                                                                      · have hr : n - 49100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 49100) + 49100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact le_w982 ⟨n - 49100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 49200
                                                                                                                                                                        · have hr : n - 49150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 49150) + 49150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact le_w983 ⟨n - 49150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 49250
                                                                                                                                                                          · have hr : n - 49200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 49200) + 49200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact le_w984 ⟨n - 49200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 49300
                                                                                                                                                                            · have hr : n - 49250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 49250) + 49250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact le_w985 ⟨n - 49250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 49350
                                                                                                                                                                              · have hr : n - 49300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 49300) + 49300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact le_w986 ⟨n - 49300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 49400
                                                                                                                                                                                · have hr : n - 49350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 49350) + 49350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact le_w987 ⟨n - 49350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 49450
                                                                                                                                                                                  · have hr : n - 49400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 49400) + 49400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact le_w988 ⟨n - 49400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 49500
                                                                                                                                                                                    · have hr : n - 49450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 49450) + 49450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact le_w989 ⟨n - 49450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 49550
                                                                                                                                                                                      · have hr : n - 49500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 49500) + 49500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact le_w990 ⟨n - 49500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 49600
                                                                                                                                                                                        · have hr : n - 49550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 49550) + 49550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact le_w991 ⟨n - 49550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 49650
                                                                                                                                                                                          · have hr : n - 49600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 49600) + 49600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact le_w992 ⟨n - 49600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 49700
                                                                                                                                                                                            · have hr : n - 49650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 49650) + 49650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact le_w993 ⟨n - 49650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 49750
                                                                                                                                                                                              · have hr : n - 49700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 49700) + 49700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact le_w994 ⟨n - 49700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 49800
                                                                                                                                                                                                · have hr : n - 49750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 49750) + 49750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact le_w995 ⟨n - 49750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 49850
                                                                                                                                                                                                  · have hr : n - 49800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 49800) + 49800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact le_w996 ⟨n - 49800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 49900
                                                                                                                                                                                                    · have hr : n - 49850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 49850) + 49850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact le_w997 ⟨n - 49850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 49950
                                                                                                                                                                                                      · have hr : n - 49900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 49900) + 49900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact le_w998 ⟨n - 49900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 50000
                                                                                                                                                                                                        · have hr : n - 49950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 49950) + 49950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact le_w999 ⟨n - 49950, hr⟩
                                                                                                                                                                                                        · omega

theorem dimF_pos_range : ∀ n, 45000 ≤ n → n < 50000 → 0 < dimF n := by
  intro n hlo hhi
  by_cases h0 : n < 45050
  · have hr : n - 45000 < 50 := by omega
    have heq : n = (n - 45000) + 45000 := by omega
    rw [heq]
    exact pos_w900 ⟨n - 45000, hr⟩
  · by_cases h1 : n < 45100
    · have hr : n - 45050 < 50 := by omega
      have heq : n = (n - 45050) + 45050 := by omega
      rw [heq]
      exact pos_w901 ⟨n - 45050, hr⟩
    · by_cases h2 : n < 45150
      · have hr : n - 45100 < 50 := by omega
        have heq : n = (n - 45100) + 45100 := by omega
        rw [heq]
        exact pos_w902 ⟨n - 45100, hr⟩
      · by_cases h3 : n < 45200
        · have hr : n - 45150 < 50 := by omega
          have heq : n = (n - 45150) + 45150 := by omega
          rw [heq]
          exact pos_w903 ⟨n - 45150, hr⟩
        · by_cases h4 : n < 45250
          · have hr : n - 45200 < 50 := by omega
            have heq : n = (n - 45200) + 45200 := by omega
            rw [heq]
            exact pos_w904 ⟨n - 45200, hr⟩
          · by_cases h5 : n < 45300
            · have hr : n - 45250 < 50 := by omega
              have heq : n = (n - 45250) + 45250 := by omega
              rw [heq]
              exact pos_w905 ⟨n - 45250, hr⟩
            · by_cases h6 : n < 45350
              · have hr : n - 45300 < 50 := by omega
                have heq : n = (n - 45300) + 45300 := by omega
                rw [heq]
                exact pos_w906 ⟨n - 45300, hr⟩
              · by_cases h7 : n < 45400
                · have hr : n - 45350 < 50 := by omega
                  have heq : n = (n - 45350) + 45350 := by omega
                  rw [heq]
                  exact pos_w907 ⟨n - 45350, hr⟩
                · by_cases h8 : n < 45450
                  · have hr : n - 45400 < 50 := by omega
                    have heq : n = (n - 45400) + 45400 := by omega
                    rw [heq]
                    exact pos_w908 ⟨n - 45400, hr⟩
                  · by_cases h9 : n < 45500
                    · have hr : n - 45450 < 50 := by omega
                      have heq : n = (n - 45450) + 45450 := by omega
                      rw [heq]
                      exact pos_w909 ⟨n - 45450, hr⟩
                    · by_cases h10 : n < 45550
                      · have hr : n - 45500 < 50 := by omega
                        have heq : n = (n - 45500) + 45500 := by omega
                        rw [heq]
                        exact pos_w910 ⟨n - 45500, hr⟩
                      · by_cases h11 : n < 45600
                        · have hr : n - 45550 < 50 := by omega
                          have heq : n = (n - 45550) + 45550 := by omega
                          rw [heq]
                          exact pos_w911 ⟨n - 45550, hr⟩
                        · by_cases h12 : n < 45650
                          · have hr : n - 45600 < 50 := by omega
                            have heq : n = (n - 45600) + 45600 := by omega
                            rw [heq]
                            exact pos_w912 ⟨n - 45600, hr⟩
                          · by_cases h13 : n < 45700
                            · have hr : n - 45650 < 50 := by omega
                              have heq : n = (n - 45650) + 45650 := by omega
                              rw [heq]
                              exact pos_w913 ⟨n - 45650, hr⟩
                            · by_cases h14 : n < 45750
                              · have hr : n - 45700 < 50 := by omega
                                have heq : n = (n - 45700) + 45700 := by omega
                                rw [heq]
                                exact pos_w914 ⟨n - 45700, hr⟩
                              · by_cases h15 : n < 45800
                                · have hr : n - 45750 < 50 := by omega
                                  have heq : n = (n - 45750) + 45750 := by omega
                                  rw [heq]
                                  exact pos_w915 ⟨n - 45750, hr⟩
                                · by_cases h16 : n < 45850
                                  · have hr : n - 45800 < 50 := by omega
                                    have heq : n = (n - 45800) + 45800 := by omega
                                    rw [heq]
                                    exact pos_w916 ⟨n - 45800, hr⟩
                                  · by_cases h17 : n < 45900
                                    · have hr : n - 45850 < 50 := by omega
                                      have heq : n = (n - 45850) + 45850 := by omega
                                      rw [heq]
                                      exact pos_w917 ⟨n - 45850, hr⟩
                                    · by_cases h18 : n < 45950
                                      · have hr : n - 45900 < 50 := by omega
                                        have heq : n = (n - 45900) + 45900 := by omega
                                        rw [heq]
                                        exact pos_w918 ⟨n - 45900, hr⟩
                                      · by_cases h19 : n < 46000
                                        · have hr : n - 45950 < 50 := by omega
                                          have heq : n = (n - 45950) + 45950 := by omega
                                          rw [heq]
                                          exact pos_w919 ⟨n - 45950, hr⟩
                                        · by_cases h20 : n < 46050
                                          · have hr : n - 46000 < 50 := by omega
                                            have heq : n = (n - 46000) + 46000 := by omega
                                            rw [heq]
                                            exact pos_w920 ⟨n - 46000, hr⟩
                                          · by_cases h21 : n < 46100
                                            · have hr : n - 46050 < 50 := by omega
                                              have heq : n = (n - 46050) + 46050 := by omega
                                              rw [heq]
                                              exact pos_w921 ⟨n - 46050, hr⟩
                                            · by_cases h22 : n < 46150
                                              · have hr : n - 46100 < 50 := by omega
                                                have heq : n = (n - 46100) + 46100 := by omega
                                                rw [heq]
                                                exact pos_w922 ⟨n - 46100, hr⟩
                                              · by_cases h23 : n < 46200
                                                · have hr : n - 46150 < 50 := by omega
                                                  have heq : n = (n - 46150) + 46150 := by omega
                                                  rw [heq]
                                                  exact pos_w923 ⟨n - 46150, hr⟩
                                                · by_cases h24 : n < 46250
                                                  · have hr : n - 46200 < 50 := by omega
                                                    have heq : n = (n - 46200) + 46200 := by omega
                                                    rw [heq]
                                                    exact pos_w924 ⟨n - 46200, hr⟩
                                                  · by_cases h25 : n < 46300
                                                    · have hr : n - 46250 < 50 := by omega
                                                      have heq : n = (n - 46250) + 46250 := by omega
                                                      rw [heq]
                                                      exact pos_w925 ⟨n - 46250, hr⟩
                                                    · by_cases h26 : n < 46350
                                                      · have hr : n - 46300 < 50 := by omega
                                                        have heq : n = (n - 46300) + 46300 := by omega
                                                        rw [heq]
                                                        exact pos_w926 ⟨n - 46300, hr⟩
                                                      · by_cases h27 : n < 46400
                                                        · have hr : n - 46350 < 50 := by omega
                                                          have heq : n = (n - 46350) + 46350 := by omega
                                                          rw [heq]
                                                          exact pos_w927 ⟨n - 46350, hr⟩
                                                        · by_cases h28 : n < 46450
                                                          · have hr : n - 46400 < 50 := by omega
                                                            have heq : n = (n - 46400) + 46400 := by omega
                                                            rw [heq]
                                                            exact pos_w928 ⟨n - 46400, hr⟩
                                                          · by_cases h29 : n < 46500
                                                            · have hr : n - 46450 < 50 := by omega
                                                              have heq : n = (n - 46450) + 46450 := by omega
                                                              rw [heq]
                                                              exact pos_w929 ⟨n - 46450, hr⟩
                                                            · by_cases h30 : n < 46550
                                                              · have hr : n - 46500 < 50 := by omega
                                                                have heq : n = (n - 46500) + 46500 := by omega
                                                                rw [heq]
                                                                exact pos_w930 ⟨n - 46500, hr⟩
                                                              · by_cases h31 : n < 46600
                                                                · have hr : n - 46550 < 50 := by omega
                                                                  have heq : n = (n - 46550) + 46550 := by omega
                                                                  rw [heq]
                                                                  exact pos_w931 ⟨n - 46550, hr⟩
                                                                · by_cases h32 : n < 46650
                                                                  · have hr : n - 46600 < 50 := by omega
                                                                    have heq : n = (n - 46600) + 46600 := by omega
                                                                    rw [heq]
                                                                    exact pos_w932 ⟨n - 46600, hr⟩
                                                                  · by_cases h33 : n < 46700
                                                                    · have hr : n - 46650 < 50 := by omega
                                                                      have heq : n = (n - 46650) + 46650 := by omega
                                                                      rw [heq]
                                                                      exact pos_w933 ⟨n - 46650, hr⟩
                                                                    · by_cases h34 : n < 46750
                                                                      · have hr : n - 46700 < 50 := by omega
                                                                        have heq : n = (n - 46700) + 46700 := by omega
                                                                        rw [heq]
                                                                        exact pos_w934 ⟨n - 46700, hr⟩
                                                                      · by_cases h35 : n < 46800
                                                                        · have hr : n - 46750 < 50 := by omega
                                                                          have heq : n = (n - 46750) + 46750 := by omega
                                                                          rw [heq]
                                                                          exact pos_w935 ⟨n - 46750, hr⟩
                                                                        · by_cases h36 : n < 46850
                                                                          · have hr : n - 46800 < 50 := by omega
                                                                            have heq : n = (n - 46800) + 46800 := by omega
                                                                            rw [heq]
                                                                            exact pos_w936 ⟨n - 46800, hr⟩
                                                                          · by_cases h37 : n < 46900
                                                                            · have hr : n - 46850 < 50 := by omega
                                                                              have heq : n = (n - 46850) + 46850 := by omega
                                                                              rw [heq]
                                                                              exact pos_w937 ⟨n - 46850, hr⟩
                                                                            · by_cases h38 : n < 46950
                                                                              · have hr : n - 46900 < 50 := by omega
                                                                                have heq : n = (n - 46900) + 46900 := by omega
                                                                                rw [heq]
                                                                                exact pos_w938 ⟨n - 46900, hr⟩
                                                                              · by_cases h39 : n < 47000
                                                                                · have hr : n - 46950 < 50 := by omega
                                                                                  have heq : n = (n - 46950) + 46950 := by omega
                                                                                  rw [heq]
                                                                                  exact pos_w939 ⟨n - 46950, hr⟩
                                                                                · by_cases h40 : n < 47050
                                                                                  · have hr : n - 47000 < 50 := by omega
                                                                                    have heq : n = (n - 47000) + 47000 := by omega
                                                                                    rw [heq]
                                                                                    exact pos_w940 ⟨n - 47000, hr⟩
                                                                                  · by_cases h41 : n < 47100
                                                                                    · have hr : n - 47050 < 50 := by omega
                                                                                      have heq : n = (n - 47050) + 47050 := by omega
                                                                                      rw [heq]
                                                                                      exact pos_w941 ⟨n - 47050, hr⟩
                                                                                    · by_cases h42 : n < 47150
                                                                                      · have hr : n - 47100 < 50 := by omega
                                                                                        have heq : n = (n - 47100) + 47100 := by omega
                                                                                        rw [heq]
                                                                                        exact pos_w942 ⟨n - 47100, hr⟩
                                                                                      · by_cases h43 : n < 47200
                                                                                        · have hr : n - 47150 < 50 := by omega
                                                                                          have heq : n = (n - 47150) + 47150 := by omega
                                                                                          rw [heq]
                                                                                          exact pos_w943 ⟨n - 47150, hr⟩
                                                                                        · by_cases h44 : n < 47250
                                                                                          · have hr : n - 47200 < 50 := by omega
                                                                                            have heq : n = (n - 47200) + 47200 := by omega
                                                                                            rw [heq]
                                                                                            exact pos_w944 ⟨n - 47200, hr⟩
                                                                                          · by_cases h45 : n < 47300
                                                                                            · have hr : n - 47250 < 50 := by omega
                                                                                              have heq : n = (n - 47250) + 47250 := by omega
                                                                                              rw [heq]
                                                                                              exact pos_w945 ⟨n - 47250, hr⟩
                                                                                            · by_cases h46 : n < 47350
                                                                                              · have hr : n - 47300 < 50 := by omega
                                                                                                have heq : n = (n - 47300) + 47300 := by omega
                                                                                                rw [heq]
                                                                                                exact pos_w946 ⟨n - 47300, hr⟩
                                                                                              · by_cases h47 : n < 47400
                                                                                                · have hr : n - 47350 < 50 := by omega
                                                                                                  have heq : n = (n - 47350) + 47350 := by omega
                                                                                                  rw [heq]
                                                                                                  exact pos_w947 ⟨n - 47350, hr⟩
                                                                                                · by_cases h48 : n < 47450
                                                                                                  · have hr : n - 47400 < 50 := by omega
                                                                                                    have heq : n = (n - 47400) + 47400 := by omega
                                                                                                    rw [heq]
                                                                                                    exact pos_w948 ⟨n - 47400, hr⟩
                                                                                                  · by_cases h49 : n < 47500
                                                                                                    · have hr : n - 47450 < 50 := by omega
                                                                                                      have heq : n = (n - 47450) + 47450 := by omega
                                                                                                      rw [heq]
                                                                                                      exact pos_w949 ⟨n - 47450, hr⟩
                                                                                                    · by_cases h50 : n < 47550
                                                                                                      · have hr : n - 47500 < 50 := by omega
                                                                                                        have heq : n = (n - 47500) + 47500 := by omega
                                                                                                        rw [heq]
                                                                                                        exact pos_w950 ⟨n - 47500, hr⟩
                                                                                                      · by_cases h51 : n < 47600
                                                                                                        · have hr : n - 47550 < 50 := by omega
                                                                                                          have heq : n = (n - 47550) + 47550 := by omega
                                                                                                          rw [heq]
                                                                                                          exact pos_w951 ⟨n - 47550, hr⟩
                                                                                                        · by_cases h52 : n < 47650
                                                                                                          · have hr : n - 47600 < 50 := by omega
                                                                                                            have heq : n = (n - 47600) + 47600 := by omega
                                                                                                            rw [heq]
                                                                                                            exact pos_w952 ⟨n - 47600, hr⟩
                                                                                                          · by_cases h53 : n < 47700
                                                                                                            · have hr : n - 47650 < 50 := by omega
                                                                                                              have heq : n = (n - 47650) + 47650 := by omega
                                                                                                              rw [heq]
                                                                                                              exact pos_w953 ⟨n - 47650, hr⟩
                                                                                                            · by_cases h54 : n < 47750
                                                                                                              · have hr : n - 47700 < 50 := by omega
                                                                                                                have heq : n = (n - 47700) + 47700 := by omega
                                                                                                                rw [heq]
                                                                                                                exact pos_w954 ⟨n - 47700, hr⟩
                                                                                                              · by_cases h55 : n < 47800
                                                                                                                · have hr : n - 47750 < 50 := by omega
                                                                                                                  have heq : n = (n - 47750) + 47750 := by omega
                                                                                                                  rw [heq]
                                                                                                                  exact pos_w955 ⟨n - 47750, hr⟩
                                                                                                                · by_cases h56 : n < 47850
                                                                                                                  · have hr : n - 47800 < 50 := by omega
                                                                                                                    have heq : n = (n - 47800) + 47800 := by omega
                                                                                                                    rw [heq]
                                                                                                                    exact pos_w956 ⟨n - 47800, hr⟩
                                                                                                                  · by_cases h57 : n < 47900
                                                                                                                    · have hr : n - 47850 < 50 := by omega
                                                                                                                      have heq : n = (n - 47850) + 47850 := by omega
                                                                                                                      rw [heq]
                                                                                                                      exact pos_w957 ⟨n - 47850, hr⟩
                                                                                                                    · by_cases h58 : n < 47950
                                                                                                                      · have hr : n - 47900 < 50 := by omega
                                                                                                                        have heq : n = (n - 47900) + 47900 := by omega
                                                                                                                        rw [heq]
                                                                                                                        exact pos_w958 ⟨n - 47900, hr⟩
                                                                                                                      · by_cases h59 : n < 48000
                                                                                                                        · have hr : n - 47950 < 50 := by omega
                                                                                                                          have heq : n = (n - 47950) + 47950 := by omega
                                                                                                                          rw [heq]
                                                                                                                          exact pos_w959 ⟨n - 47950, hr⟩
                                                                                                                        · by_cases h60 : n < 48050
                                                                                                                          · have hr : n - 48000 < 50 := by omega
                                                                                                                            have heq : n = (n - 48000) + 48000 := by omega
                                                                                                                            rw [heq]
                                                                                                                            exact pos_w960 ⟨n - 48000, hr⟩
                                                                                                                          · by_cases h61 : n < 48100
                                                                                                                            · have hr : n - 48050 < 50 := by omega
                                                                                                                              have heq : n = (n - 48050) + 48050 := by omega
                                                                                                                              rw [heq]
                                                                                                                              exact pos_w961 ⟨n - 48050, hr⟩
                                                                                                                            · by_cases h62 : n < 48150
                                                                                                                              · have hr : n - 48100 < 50 := by omega
                                                                                                                                have heq : n = (n - 48100) + 48100 := by omega
                                                                                                                                rw [heq]
                                                                                                                                exact pos_w962 ⟨n - 48100, hr⟩
                                                                                                                              · by_cases h63 : n < 48200
                                                                                                                                · have hr : n - 48150 < 50 := by omega
                                                                                                                                  have heq : n = (n - 48150) + 48150 := by omega
                                                                                                                                  rw [heq]
                                                                                                                                  exact pos_w963 ⟨n - 48150, hr⟩
                                                                                                                                · by_cases h64 : n < 48250
                                                                                                                                  · have hr : n - 48200 < 50 := by omega
                                                                                                                                    have heq : n = (n - 48200) + 48200 := by omega
                                                                                                                                    rw [heq]
                                                                                                                                    exact pos_w964 ⟨n - 48200, hr⟩
                                                                                                                                  · by_cases h65 : n < 48300
                                                                                                                                    · have hr : n - 48250 < 50 := by omega
                                                                                                                                      have heq : n = (n - 48250) + 48250 := by omega
                                                                                                                                      rw [heq]
                                                                                                                                      exact pos_w965 ⟨n - 48250, hr⟩
                                                                                                                                    · by_cases h66 : n < 48350
                                                                                                                                      · have hr : n - 48300 < 50 := by omega
                                                                                                                                        have heq : n = (n - 48300) + 48300 := by omega
                                                                                                                                        rw [heq]
                                                                                                                                        exact pos_w966 ⟨n - 48300, hr⟩
                                                                                                                                      · by_cases h67 : n < 48400
                                                                                                                                        · have hr : n - 48350 < 50 := by omega
                                                                                                                                          have heq : n = (n - 48350) + 48350 := by omega
                                                                                                                                          rw [heq]
                                                                                                                                          exact pos_w967 ⟨n - 48350, hr⟩
                                                                                                                                        · by_cases h68 : n < 48450
                                                                                                                                          · have hr : n - 48400 < 50 := by omega
                                                                                                                                            have heq : n = (n - 48400) + 48400 := by omega
                                                                                                                                            rw [heq]
                                                                                                                                            exact pos_w968 ⟨n - 48400, hr⟩
                                                                                                                                          · by_cases h69 : n < 48500
                                                                                                                                            · have hr : n - 48450 < 50 := by omega
                                                                                                                                              have heq : n = (n - 48450) + 48450 := by omega
                                                                                                                                              rw [heq]
                                                                                                                                              exact pos_w969 ⟨n - 48450, hr⟩
                                                                                                                                            · by_cases h70 : n < 48550
                                                                                                                                              · have hr : n - 48500 < 50 := by omega
                                                                                                                                                have heq : n = (n - 48500) + 48500 := by omega
                                                                                                                                                rw [heq]
                                                                                                                                                exact pos_w970 ⟨n - 48500, hr⟩
                                                                                                                                              · by_cases h71 : n < 48600
                                                                                                                                                · have hr : n - 48550 < 50 := by omega
                                                                                                                                                  have heq : n = (n - 48550) + 48550 := by omega
                                                                                                                                                  rw [heq]
                                                                                                                                                  exact pos_w971 ⟨n - 48550, hr⟩
                                                                                                                                                · by_cases h72 : n < 48650
                                                                                                                                                  · have hr : n - 48600 < 50 := by omega
                                                                                                                                                    have heq : n = (n - 48600) + 48600 := by omega
                                                                                                                                                    rw [heq]
                                                                                                                                                    exact pos_w972 ⟨n - 48600, hr⟩
                                                                                                                                                  · by_cases h73 : n < 48700
                                                                                                                                                    · have hr : n - 48650 < 50 := by omega
                                                                                                                                                      have heq : n = (n - 48650) + 48650 := by omega
                                                                                                                                                      rw [heq]
                                                                                                                                                      exact pos_w973 ⟨n - 48650, hr⟩
                                                                                                                                                    · by_cases h74 : n < 48750
                                                                                                                                                      · have hr : n - 48700 < 50 := by omega
                                                                                                                                                        have heq : n = (n - 48700) + 48700 := by omega
                                                                                                                                                        rw [heq]
                                                                                                                                                        exact pos_w974 ⟨n - 48700, hr⟩
                                                                                                                                                      · by_cases h75 : n < 48800
                                                                                                                                                        · have hr : n - 48750 < 50 := by omega
                                                                                                                                                          have heq : n = (n - 48750) + 48750 := by omega
                                                                                                                                                          rw [heq]
                                                                                                                                                          exact pos_w975 ⟨n - 48750, hr⟩
                                                                                                                                                        · by_cases h76 : n < 48850
                                                                                                                                                          · have hr : n - 48800 < 50 := by omega
                                                                                                                                                            have heq : n = (n - 48800) + 48800 := by omega
                                                                                                                                                            rw [heq]
                                                                                                                                                            exact pos_w976 ⟨n - 48800, hr⟩
                                                                                                                                                          · by_cases h77 : n < 48900
                                                                                                                                                            · have hr : n - 48850 < 50 := by omega
                                                                                                                                                              have heq : n = (n - 48850) + 48850 := by omega
                                                                                                                                                              rw [heq]
                                                                                                                                                              exact pos_w977 ⟨n - 48850, hr⟩
                                                                                                                                                            · by_cases h78 : n < 48950
                                                                                                                                                              · have hr : n - 48900 < 50 := by omega
                                                                                                                                                                have heq : n = (n - 48900) + 48900 := by omega
                                                                                                                                                                rw [heq]
                                                                                                                                                                exact pos_w978 ⟨n - 48900, hr⟩
                                                                                                                                                              · by_cases h79 : n < 49000
                                                                                                                                                                · have hr : n - 48950 < 50 := by omega
                                                                                                                                                                  have heq : n = (n - 48950) + 48950 := by omega
                                                                                                                                                                  rw [heq]
                                                                                                                                                                  exact pos_w979 ⟨n - 48950, hr⟩
                                                                                                                                                                · by_cases h80 : n < 49050
                                                                                                                                                                  · have hr : n - 49000 < 50 := by omega
                                                                                                                                                                    have heq : n = (n - 49000) + 49000 := by omega
                                                                                                                                                                    rw [heq]
                                                                                                                                                                    exact pos_w980 ⟨n - 49000, hr⟩
                                                                                                                                                                  · by_cases h81 : n < 49100
                                                                                                                                                                    · have hr : n - 49050 < 50 := by omega
                                                                                                                                                                      have heq : n = (n - 49050) + 49050 := by omega
                                                                                                                                                                      rw [heq]
                                                                                                                                                                      exact pos_w981 ⟨n - 49050, hr⟩
                                                                                                                                                                    · by_cases h82 : n < 49150
                                                                                                                                                                      · have hr : n - 49100 < 50 := by omega
                                                                                                                                                                        have heq : n = (n - 49100) + 49100 := by omega
                                                                                                                                                                        rw [heq]
                                                                                                                                                                        exact pos_w982 ⟨n - 49100, hr⟩
                                                                                                                                                                      · by_cases h83 : n < 49200
                                                                                                                                                                        · have hr : n - 49150 < 50 := by omega
                                                                                                                                                                          have heq : n = (n - 49150) + 49150 := by omega
                                                                                                                                                                          rw [heq]
                                                                                                                                                                          exact pos_w983 ⟨n - 49150, hr⟩
                                                                                                                                                                        · by_cases h84 : n < 49250
                                                                                                                                                                          · have hr : n - 49200 < 50 := by omega
                                                                                                                                                                            have heq : n = (n - 49200) + 49200 := by omega
                                                                                                                                                                            rw [heq]
                                                                                                                                                                            exact pos_w984 ⟨n - 49200, hr⟩
                                                                                                                                                                          · by_cases h85 : n < 49300
                                                                                                                                                                            · have hr : n - 49250 < 50 := by omega
                                                                                                                                                                              have heq : n = (n - 49250) + 49250 := by omega
                                                                                                                                                                              rw [heq]
                                                                                                                                                                              exact pos_w985 ⟨n - 49250, hr⟩
                                                                                                                                                                            · by_cases h86 : n < 49350
                                                                                                                                                                              · have hr : n - 49300 < 50 := by omega
                                                                                                                                                                                have heq : n = (n - 49300) + 49300 := by omega
                                                                                                                                                                                rw [heq]
                                                                                                                                                                                exact pos_w986 ⟨n - 49300, hr⟩
                                                                                                                                                                              · by_cases h87 : n < 49400
                                                                                                                                                                                · have hr : n - 49350 < 50 := by omega
                                                                                                                                                                                  have heq : n = (n - 49350) + 49350 := by omega
                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                  exact pos_w987 ⟨n - 49350, hr⟩
                                                                                                                                                                                · by_cases h88 : n < 49450
                                                                                                                                                                                  · have hr : n - 49400 < 50 := by omega
                                                                                                                                                                                    have heq : n = (n - 49400) + 49400 := by omega
                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                    exact pos_w988 ⟨n - 49400, hr⟩
                                                                                                                                                                                  · by_cases h89 : n < 49500
                                                                                                                                                                                    · have hr : n - 49450 < 50 := by omega
                                                                                                                                                                                      have heq : n = (n - 49450) + 49450 := by omega
                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                      exact pos_w989 ⟨n - 49450, hr⟩
                                                                                                                                                                                    · by_cases h90 : n < 49550
                                                                                                                                                                                      · have hr : n - 49500 < 50 := by omega
                                                                                                                                                                                        have heq : n = (n - 49500) + 49500 := by omega
                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                        exact pos_w990 ⟨n - 49500, hr⟩
                                                                                                                                                                                      · by_cases h91 : n < 49600
                                                                                                                                                                                        · have hr : n - 49550 < 50 := by omega
                                                                                                                                                                                          have heq : n = (n - 49550) + 49550 := by omega
                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                          exact pos_w991 ⟨n - 49550, hr⟩
                                                                                                                                                                                        · by_cases h92 : n < 49650
                                                                                                                                                                                          · have hr : n - 49600 < 50 := by omega
                                                                                                                                                                                            have heq : n = (n - 49600) + 49600 := by omega
                                                                                                                                                                                            rw [heq]
                                                                                                                                                                                            exact pos_w992 ⟨n - 49600, hr⟩
                                                                                                                                                                                          · by_cases h93 : n < 49700
                                                                                                                                                                                            · have hr : n - 49650 < 50 := by omega
                                                                                                                                                                                              have heq : n = (n - 49650) + 49650 := by omega
                                                                                                                                                                                              rw [heq]
                                                                                                                                                                                              exact pos_w993 ⟨n - 49650, hr⟩
                                                                                                                                                                                            · by_cases h94 : n < 49750
                                                                                                                                                                                              · have hr : n - 49700 < 50 := by omega
                                                                                                                                                                                                have heq : n = (n - 49700) + 49700 := by omega
                                                                                                                                                                                                rw [heq]
                                                                                                                                                                                                exact pos_w994 ⟨n - 49700, hr⟩
                                                                                                                                                                                              · by_cases h95 : n < 49800
                                                                                                                                                                                                · have hr : n - 49750 < 50 := by omega
                                                                                                                                                                                                  have heq : n = (n - 49750) + 49750 := by omega
                                                                                                                                                                                                  rw [heq]
                                                                                                                                                                                                  exact pos_w995 ⟨n - 49750, hr⟩
                                                                                                                                                                                                · by_cases h96 : n < 49850
                                                                                                                                                                                                  · have hr : n - 49800 < 50 := by omega
                                                                                                                                                                                                    have heq : n = (n - 49800) + 49800 := by omega
                                                                                                                                                                                                    rw [heq]
                                                                                                                                                                                                    exact pos_w996 ⟨n - 49800, hr⟩
                                                                                                                                                                                                  · by_cases h97 : n < 49900
                                                                                                                                                                                                    · have hr : n - 49850 < 50 := by omega
                                                                                                                                                                                                      have heq : n = (n - 49850) + 49850 := by omega
                                                                                                                                                                                                      rw [heq]
                                                                                                                                                                                                      exact pos_w997 ⟨n - 49850, hr⟩
                                                                                                                                                                                                    · by_cases h98 : n < 49950
                                                                                                                                                                                                      · have hr : n - 49900 < 50 := by omega
                                                                                                                                                                                                        have heq : n = (n - 49900) + 49900 := by omega
                                                                                                                                                                                                        rw [heq]
                                                                                                                                                                                                        exact pos_w998 ⟨n - 49900, hr⟩
                                                                                                                                                                                                      · by_cases h99 : n < 50000
                                                                                                                                                                                                        · have hr : n - 49950 < 50 := by omega
                                                                                                                                                                                                          have heq : n = (n - 49950) + 49950 := by omega
                                                                                                                                                                                                          rw [heq]
                                                                                                                                                                                                          exact pos_w999 ⟨n - 49950, hr⟩
                                                                                                                                                                                                        · omega

end IntMul.Kappa.R8.Bit.Oppbank.DimBound9


