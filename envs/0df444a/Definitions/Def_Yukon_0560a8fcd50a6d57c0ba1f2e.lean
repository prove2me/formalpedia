-- Prove2me | Definitions.Def_Yukon_0560a8fcd50a6d57c0ba1f2e
-- name    : Yukon_0560a8fcd50a6d57c0ba1f2e
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:44:40.217289+00:00
-- url     : https://prove2.me/theorems/094fde03-b3a1-4dc6-96b5-e575de490d4a
-- title:
--   Relative certificate source part 10/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_0560a8fcd50a6d57c0ba1f2e
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiMTJhNWQ5MGRhYzIyNTI3OTFmMzg3M2ZhMGQ5Y2M4Y2RhNTQ4ZDQ4ZmVhNjAyMWFhZGE3MzEyMWIwM2UxNzBkNyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uXzA1NjBhOGZjZDUwYTZkNTdjMGJhMWYyZSIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uXzA1NjBhOGZjZDUwYTZkNTdjMGJhMWYyZSIsInYiOjJ9]

import Definitions.Def_Yukon_93f639d3938205e1e2162e83
import Definitions.Def_Yukon_e757298719adf05c20287f89












































































































































































































































































































































































set_option backward.isDefEq.respectTransparency.types false
/-! Saved witness SHA256: c5a3d79401563549e3da246da1fa707d32f52f28e1c561a2e007749bd764d43f.
Each row and both total endpoints are kernel checked; the generic
proof covers every intermediate total and the infinite weight tail. -/
namespace ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 50000
set_option Elab.async false
open RelativeCertificate6814

def b256 : List (Rectangle × FastWitness) := [(r2048,⟨67,43,43⟩),(r2049,⟨67,43,43⟩),(r2050,⟨67,43,43⟩),(r2051,⟨67,43,43⟩),(r2052,⟨67,43,43⟩),(r2053,⟨67,43,43⟩),(r2054,⟨67,43,43⟩),(r2055,⟨67,43,43⟩)]
theorem checked256 : fastCheckList band b256=true := by decide +kernel

def b257 : List (Rectangle × FastWitness) := [(r2056,⟨67,43,43⟩),(r2057,⟨67,43,43⟩),(r2058,⟨67,43,43⟩),(r2059,⟨67,43,43⟩),(r2060,⟨67,43,43⟩),(r2061,⟨67,43,43⟩),(r2062,⟨67,43,43⟩),(r2063,⟨67,43,43⟩)]
theorem checked257 : fastCheckList band b257=true := by decide +kernel

def b258 : List (Rectangle × FastWitness) := [(r2064,⟨67,43,43⟩),(r2065,⟨67,43,43⟩),(r2066,⟨67,43,43⟩),(r2067,⟨67,43,43⟩),(r2068,⟨67,43,43⟩),(r2069,⟨67,43,43⟩),(r2070,⟨67,43,43⟩),(r2071,⟨67,43,43⟩)]
theorem checked258 : fastCheckList band b258=true := by decide +kernel

def b259 : List (Rectangle × FastWitness) := [(r2072,⟨67,43,43⟩),(r2073,⟨67,43,43⟩),(r2074,⟨67,43,43⟩),(r2075,⟨67,43,43⟩),(r2076,⟨67,43,43⟩),(r2077,⟨67,43,43⟩),(r2078,⟨67,43,43⟩),(r2079,⟨67,43,43⟩)]
theorem checked259 : fastCheckList band b259=true := by decide +kernel

def b260 : List (Rectangle × FastWitness) := [(r2080,⟨67,43,43⟩),(r2081,⟨67,43,43⟩),(r2082,⟨67,43,43⟩),(r2083,⟨67,43,43⟩),(r2084,⟨67,43,43⟩),(r2085,⟨67,43,43⟩),(r2086,⟨67,43,43⟩),(r2087,⟨67,43,43⟩)]
theorem checked260 : fastCheckList band b260=true := by decide +kernel

def b261 : List (Rectangle × FastWitness) := [(r2088,⟨67,43,43⟩),(r2089,⟨67,43,43⟩),(r2090,⟨67,43,43⟩),(r2091,⟨67,43,43⟩),(r2092,⟨67,43,43⟩),(r2093,⟨67,43,43⟩),(r2094,⟨67,43,43⟩),(r2095,⟨67,43,43⟩)]
theorem checked261 : fastCheckList band b261=true := by decide +kernel

def b262 : List (Rectangle × FastWitness) := [(r2096,⟨67,43,43⟩),(r2097,⟨67,43,43⟩),(r2098,⟨67,43,43⟩),(r2099,⟨67,43,43⟩),(r2100,⟨67,43,43⟩),(r2101,⟨67,43,43⟩),(r2102,⟨67,43,43⟩),(r2103,⟨67,43,43⟩)]
theorem checked262 : fastCheckList band b262=true := by decide +kernel

def b263 : List (Rectangle × FastWitness) := [(r2104,⟨67,43,43⟩),(r2105,⟨67,43,43⟩),(r2106,⟨67,43,43⟩),(r2107,⟨67,43,43⟩),(r2108,⟨67,43,43⟩),(r2109,⟨67,43,43⟩),(r2110,⟨67,43,43⟩),(r2111,⟨67,43,43⟩)]
theorem checked263 : fastCheckList band b263=true := by decide +kernel

def b264 : List (Rectangle × FastWitness) := [(r2112,⟨67,43,43⟩),(r2113,⟨67,43,43⟩),(r2114,⟨67,43,43⟩),(r2115,⟨67,43,43⟩),(r2116,⟨67,43,43⟩),(r2117,⟨67,43,43⟩),(r2118,⟨67,43,43⟩),(r2119,⟨67,43,43⟩)]
theorem checked264 : fastCheckList band b264=true := by decide +kernel

def b265 : List (Rectangle × FastWitness) := [(r2120,⟨67,43,43⟩),(r2121,⟨67,43,43⟩),(r2122,⟨67,43,43⟩),(r2123,⟨67,43,43⟩),(r2124,⟨67,43,43⟩),(r2125,⟨67,43,43⟩),(r2126,⟨67,43,43⟩),(r2127,⟨67,43,43⟩)]
theorem checked265 : fastCheckList band b265=true := by decide +kernel

def b266 : List (Rectangle × FastWitness) := [(r2128,⟨67,43,43⟩),(r2129,⟨67,43,43⟩),(r2130,⟨67,43,43⟩),(r2131,⟨67,43,43⟩),(r2132,⟨67,43,43⟩),(r2133,⟨67,43,43⟩),(r2134,⟨67,43,43⟩),(r2135,⟨67,43,43⟩)]
theorem checked266 : fastCheckList band b266=true := by decide +kernel

def b267 : List (Rectangle × FastWitness) := [(r2136,⟨67,43,43⟩),(r2137,⟨67,43,43⟩),(r2138,⟨67,43,43⟩),(r2139,⟨67,43,43⟩),(r2140,⟨67,43,43⟩),(r2141,⟨67,43,43⟩),(r2142,⟨67,43,43⟩),(r2143,⟨67,43,43⟩)]
theorem checked267 : fastCheckList band b267=true := by decide +kernel

def b268 : List (Rectangle × FastWitness) := [(r2144,⟨67,43,43⟩),(r2145,⟨67,43,43⟩),(r2146,⟨67,43,43⟩),(r2147,⟨67,43,43⟩),(r2148,⟨67,43,43⟩),(r2149,⟨67,43,43⟩),(r2150,⟨67,43,43⟩),(r2151,⟨67,43,43⟩)]
theorem checked268 : fastCheckList band b268=true := by decide +kernel

def b269 : List (Rectangle × FastWitness) := [(r2152,⟨67,43,43⟩),(r2153,⟨67,43,43⟩),(r2154,⟨67,43,43⟩),(r2155,⟨67,43,43⟩),(r2156,⟨67,43,43⟩),(r2157,⟨67,43,43⟩),(r2158,⟨67,43,43⟩),(r2159,⟨67,43,43⟩)]
theorem checked269 : fastCheckList band b269=true := by decide +kernel

def b270 : List (Rectangle × FastWitness) := [(r2160,⟨67,43,43⟩),(r2161,⟨67,43,43⟩),(r2162,⟨67,43,43⟩),(r2163,⟨67,43,43⟩),(r2164,⟨67,43,43⟩),(r2165,⟨67,43,43⟩),(r2166,⟨67,43,43⟩),(r2167,⟨67,43,43⟩)]
theorem checked270 : fastCheckList band b270=true := by decide +kernel

def b271 : List (Rectangle × FastWitness) := [(r2168,⟨67,43,43⟩),(r2169,⟨67,43,43⟩),(r2170,⟨67,43,43⟩),(r2171,⟨67,43,43⟩),(r2172,⟨67,43,43⟩),(r2173,⟨67,43,43⟩),(r2174,⟨67,43,43⟩),(r2175,⟨67,43,43⟩)]
theorem checked271 : fastCheckList band b271=true := by decide +kernel

def b272 : List (Rectangle × FastWitness) := [(r2176,⟨67,43,43⟩),(r2177,⟨67,43,44⟩),(r2178,⟨67,43,44⟩),(r2179,⟨67,43,44⟩),(r2180,⟨67,43,44⟩),(r2181,⟨67,43,44⟩),(r2182,⟨67,43,44⟩),(r2183,⟨67,43,44⟩)]
theorem checked272 : fastCheckList band b272=true := by decide +kernel

def b273 : List (Rectangle × FastWitness) := [(r2184,⟨67,44,44⟩),(r2185,⟨67,44,44⟩),(r2186,⟨67,44,44⟩),(r2187,⟨67,44,44⟩),(r2188,⟨67,44,44⟩),(r2189,⟨67,44,44⟩),(r2190,⟨67,44,44⟩),(r2191,⟨67,44,44⟩)]
theorem checked273 : fastCheckList band b273=true := by decide +kernel

def b274 : List (Rectangle × FastWitness) := [(r2192,⟨67,44,44⟩),(r2193,⟨67,44,44⟩),(r2194,⟨67,44,44⟩),(r2195,⟨67,44,44⟩),(r2196,⟨67,44,44⟩),(r2197,⟨67,44,44⟩),(r2198,⟨67,44,44⟩),(r2199,⟨67,44,44⟩)]
theorem checked274 : fastCheckList band b274=true := by decide +kernel

def b275 : List (Rectangle × FastWitness) := [(r2200,⟨67,44,44⟩),(r2201,⟨67,44,44⟩),(r2202,⟨67,44,44⟩),(r2203,⟨67,44,44⟩),(r2204,⟨67,44,44⟩),(r2205,⟨67,44,44⟩),(r2206,⟨67,44,44⟩),(r2207,⟨67,44,44⟩)]
theorem checked275 : fastCheckList band b275=true := by decide +kernel

def b276 : List (Rectangle × FastWitness) := [(r2208,⟨67,44,44⟩),(r2209,⟨67,44,44⟩),(r2210,⟨67,44,44⟩),(r2211,⟨67,44,44⟩),(r2212,⟨67,44,44⟩),(r2213,⟨67,44,44⟩),(r2214,⟨67,44,44⟩),(r2215,⟨67,44,44⟩)]
theorem checked276 : fastCheckList band b276=true := by decide +kernel

def b277 : List (Rectangle × FastWitness) := [(r2216,⟨67,44,44⟩),(r2217,⟨67,44,44⟩),(r2218,⟨67,44,44⟩),(r2219,⟨67,44,44⟩),(r2220,⟨67,44,44⟩),(r2221,⟨67,44,44⟩),(r2222,⟨67,44,44⟩),(r2223,⟨67,44,44⟩)]
theorem checked277 : fastCheckList band b277=true := by decide +kernel

def b278 : List (Rectangle × FastWitness) := [(r2224,⟨67,44,44⟩),(r2225,⟨67,44,44⟩),(r2226,⟨67,44,44⟩),(r2227,⟨67,44,44⟩),(r2228,⟨67,44,44⟩),(r2229,⟨67,44,44⟩),(r2230,⟨67,44,44⟩),(r2231,⟨67,44,44⟩)]
theorem checked278 : fastCheckList band b278=true := by decide +kernel

def b279 : List (Rectangle × FastWitness) := [(r2232,⟨67,44,44⟩),(r2233,⟨67,44,44⟩),(r2234,⟨67,44,44⟩),(r2235,⟨67,44,44⟩),(r2236,⟨67,44,44⟩),(r2237,⟨67,44,44⟩),(r2238,⟨67,44,44⟩),(r2239,⟨67,44,44⟩)]
theorem checked279 : fastCheckList band b279=true := by decide +kernel

def b280 : List (Rectangle × FastWitness) := [(r2240,⟨67,44,44⟩),(r2241,⟨67,44,44⟩),(r2242,⟨67,44,44⟩),(r2243,⟨67,44,44⟩),(r2244,⟨67,44,44⟩),(r2245,⟨67,44,44⟩),(r2246,⟨67,44,44⟩),(r2247,⟨67,44,44⟩)]
theorem checked280 : fastCheckList band b280=true := by decide +kernel

def b281 : List (Rectangle × FastWitness) := [(r2248,⟨67,44,44⟩),(r2249,⟨67,44,44⟩),(r2250,⟨67,44,44⟩),(r2251,⟨67,44,44⟩),(r2252,⟨67,44,44⟩),(r2253,⟨67,44,44⟩),(r2254,⟨67,44,44⟩),(r2255,⟨67,44,44⟩)]
theorem checked281 : fastCheckList band b281=true := by decide +kernel

def b282 : List (Rectangle × FastWitness) := [(r2256,⟨67,44,44⟩),(r2257,⟨67,44,44⟩),(r2258,⟨67,44,44⟩),(r2259,⟨67,45,45⟩),(r2260,⟨67,45,45⟩),(r2261,⟨67,45,45⟩),(r2262,⟨67,45,45⟩),(r2263,⟨67,45,45⟩)]
theorem checked282 : fastCheckList band b282=true := by decide +kernel

def b283 : List (Rectangle × FastWitness) := [(r2264,⟨67,45,45⟩),(r2265,⟨67,45,45⟩),(r2266,⟨67,45,45⟩),(r2267,⟨67,45,45⟩),(r2268,⟨67,45,45⟩),(r2269,⟨67,45,45⟩),(r2270,⟨67,45,45⟩),(r2271,⟨67,45,45⟩)]
theorem checked283 : fastCheckList band b283=true := by decide +kernel

def b284 : List (Rectangle × FastWitness) := [(r2272,⟨67,45,45⟩),(r2273,⟨67,45,45⟩),(r2274,⟨67,45,45⟩),(r2275,⟨67,45,45⟩),(r2276,⟨67,45,45⟩),(r2277,⟨67,45,45⟩),(r2278,⟨67,45,45⟩),(r2279,⟨67,45,45⟩)]
theorem checked284 : fastCheckList band b284=true := by decide +kernel

def b285 : List (Rectangle × FastWitness) := [(r2280,⟨67,45,45⟩),(r2281,⟨67,45,45⟩),(r2282,⟨67,45,45⟩),(r2283,⟨67,45,45⟩),(r2284,⟨67,45,45⟩),(r2285,⟨67,45,45⟩),(r2286,⟨67,45,45⟩),(r2287,⟨67,45,45⟩)]
theorem checked285 : fastCheckList band b285=true := by decide +kernel

def b286 : List (Rectangle × FastWitness) := [(r2288,⟨67,45,45⟩),(r2289,⟨67,45,45⟩),(r2290,⟨67,45,45⟩),(r2291,⟨67,45,45⟩),(r2292,⟨67,45,45⟩),(r2293,⟨67,45,45⟩),(r2294,⟨67,45,45⟩),(r2295,⟨67,45,45⟩)]
theorem checked286 : fastCheckList band b286=true := by decide +kernel

def b287 : List (Rectangle × FastWitness) := [(r2296,⟨67,45,45⟩),(r2297,⟨67,45,45⟩),(r2298,⟨67,45,45⟩),(r2299,⟨67,45,45⟩),(r2300,⟨67,45,45⟩),(r2301,⟨67,45,45⟩),(r2302,⟨67,45,45⟩),(r2303,⟨67,45,45⟩)]
theorem checked287 : fastCheckList band b287=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


