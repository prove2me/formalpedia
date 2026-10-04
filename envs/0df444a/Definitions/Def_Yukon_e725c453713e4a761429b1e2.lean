-- Prove2me | Definitions.Def_Yukon_e725c453713e4a761429b1e2
-- name    : Yukon_e725c453713e4a761429b1e2
-- status  : Definition
-- author  : @yukon
-- created : 2026-10-03T05:41:07.864598+00:00
-- url     : https://prove2.me/theorems/d1b70123-e03d-4e57-82f1-a65ad2076c9a
-- title:
--   Relative certificate source part 9/13
-- statement:
--   Source module ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast. Reviewed historical port from Lean 4.32.2 to 4.33.1: compatible proof bodies, equivalent notation expansion, and omission of unused tooling/declarations. Retained statements and mathematical definitions preserve the original meaning. Original source: https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
-- source:
--   https://github.com/proximity-prize/proximity-prize/blob/9008f0e2b2edb0647da15baac454a68072f0ba29/ProximityPrize/SubmissionLower/RelativeCertR13B54T3429To3499Fast.lean
--
--   yukon-proof-operation:certificate-r13-b54-module-Yukon_e725c453713e4a761429b1e2
--   [yukon-proof-receipt:eyJlbnZpcm9ubWVudCI6eyJtYXRobGliUmV2IjoiMGRmNDQ0YTM2MGVhYTYwYWI4YzExZGNhNTFhODZhZjY5Mjk1NTQ3NCIsInRvb2xjaGFpbiI6ImxlYW5wcm92ZXIvbGVhbjQ6djQuMzMuMSJ9LCJoYXNoIjoiYmVlM2Y4NzJlYWQzZmUxZjc1OTRjZGRkNzZjOGIwY2RmNzY1MzEzZDc4YjZjMjQ5M2Y1NGVlNDcxN2JmMDQwYyIsImtpbmQiOiJkZWZpbml0aW9uIiwibWFya2VyIjoieXVrb24tcHJvb2Ytb3BlcmF0aW9uOmNlcnRpZmljYXRlLXIxMy1iNTQtbW9kdWxlLVl1a29uX2U3MjVjNDUzNzEzZTRhNzYxNDI5YjFlMiIsInRhZyI6ImJldHRlci1jb2RlcyIsInRhcmdldCI6Ill1a29uX2U3MjVjNDUzNzEzZTRhNzYxNDI5YjFlMiIsInYiOjJ9]

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

def b224 : List (Rectangle × FastWitness) := [(r1792,⟨67,41,41⟩),(r1793,⟨67,41,41⟩),(r1794,⟨67,41,41⟩),(r1795,⟨67,41,41⟩),(r1796,⟨67,41,41⟩),(r1797,⟨67,41,41⟩),(r1798,⟨67,41,41⟩),(r1799,⟨67,41,41⟩)]
theorem checked224 : fastCheckList band b224=true := by decide +kernel

def b225 : List (Rectangle × FastWitness) := [(r1800,⟨67,41,41⟩),(r1801,⟨67,41,41⟩),(r1802,⟨67,41,41⟩),(r1803,⟨67,41,41⟩),(r1804,⟨67,41,41⟩),(r1805,⟨67,41,41⟩),(r1806,⟨67,41,41⟩),(r1807,⟨67,41,41⟩)]
theorem checked225 : fastCheckList band b225=true := by decide +kernel

def b226 : List (Rectangle × FastWitness) := [(r1808,⟨67,41,41⟩),(r1809,⟨67,41,41⟩),(r1810,⟨67,41,41⟩),(r1811,⟨67,41,42⟩),(r1812,⟨67,41,42⟩),(r1813,⟨67,41,42⟩),(r1814,⟨67,42,42⟩),(r1815,⟨67,42,42⟩)]
theorem checked226 : fastCheckList band b226=true := by decide +kernel

def b227 : List (Rectangle × FastWitness) := [(r1816,⟨67,42,42⟩),(r1817,⟨67,42,42⟩),(r1818,⟨67,42,42⟩),(r1819,⟨67,42,42⟩),(r1820,⟨67,42,42⟩),(r1821,⟨67,42,42⟩),(r1822,⟨67,42,42⟩),(r1823,⟨67,42,42⟩)]
theorem checked227 : fastCheckList band b227=true := by decide +kernel

def b228 : List (Rectangle × FastWitness) := [(r1824,⟨67,42,42⟩),(r1825,⟨67,42,42⟩),(r1826,⟨67,42,42⟩),(r1827,⟨67,42,42⟩),(r1828,⟨67,42,42⟩),(r1829,⟨67,42,42⟩),(r1830,⟨67,42,42⟩),(r1831,⟨67,42,42⟩)]
theorem checked228 : fastCheckList band b228=true := by decide +kernel

def b229 : List (Rectangle × FastWitness) := [(r1832,⟨67,42,42⟩),(r1833,⟨67,42,42⟩),(r1834,⟨67,42,42⟩),(r1835,⟨67,42,42⟩),(r1836,⟨67,42,42⟩),(r1837,⟨67,42,42⟩),(r1838,⟨67,42,42⟩),(r1839,⟨67,42,42⟩)]
theorem checked229 : fastCheckList band b229=true := by decide +kernel

def b230 : List (Rectangle × FastWitness) := [(r1840,⟨67,42,42⟩),(r1841,⟨67,42,42⟩),(r1842,⟨67,42,42⟩),(r1843,⟨67,42,42⟩),(r1844,⟨67,42,42⟩),(r1845,⟨67,42,42⟩),(r1846,⟨67,42,42⟩),(r1847,⟨67,42,42⟩)]
theorem checked230 : fastCheckList band b230=true := by decide +kernel

def b231 : List (Rectangle × FastWitness) := [(r1848,⟨67,42,42⟩),(r1849,⟨67,42,42⟩),(r1850,⟨67,42,42⟩),(r1851,⟨67,42,42⟩),(r1852,⟨67,42,42⟩),(r1853,⟨67,42,42⟩),(r1854,⟨67,42,42⟩),(r1855,⟨67,42,42⟩)]
theorem checked231 : fastCheckList band b231=true := by decide +kernel

def b232 : List (Rectangle × FastWitness) := [(r1856,⟨67,42,42⟩),(r1857,⟨67,42,42⟩),(r1858,⟨67,42,42⟩),(r1859,⟨67,42,42⟩),(r1860,⟨67,42,42⟩),(r1861,⟨67,42,42⟩),(r1862,⟨67,42,42⟩),(r1863,⟨67,42,42⟩)]
theorem checked232 : fastCheckList band b232=true := by decide +kernel

def b233 : List (Rectangle × FastWitness) := [(r1864,⟨67,42,42⟩),(r1865,⟨67,42,42⟩),(r1866,⟨67,42,42⟩),(r1867,⟨67,42,42⟩),(r1868,⟨67,42,42⟩),(r1869,⟨67,42,42⟩),(r1870,⟨67,42,42⟩),(r1871,⟨67,42,42⟩)]
theorem checked233 : fastCheckList band b233=true := by decide +kernel

def b234 : List (Rectangle × FastWitness) := [(r1872,⟨67,42,42⟩),(r1873,⟨67,42,42⟩),(r1874,⟨67,42,42⟩),(r1875,⟨67,42,42⟩),(r1876,⟨67,42,42⟩),(r1877,⟨67,42,42⟩),(r1878,⟨67,42,42⟩),(r1879,⟨67,42,42⟩)]
theorem checked234 : fastCheckList band b234=true := by decide +kernel

def b235 : List (Rectangle × FastWitness) := [(r1880,⟨67,42,42⟩),(r1881,⟨67,42,42⟩),(r1882,⟨67,42,42⟩),(r1883,⟨67,42,42⟩),(r1884,⟨67,42,42⟩),(r1885,⟨67,42,42⟩),(r1886,⟨67,42,42⟩),(r1887,⟨67,42,42⟩)]
theorem checked235 : fastCheckList band b235=true := by decide +kernel

def b236 : List (Rectangle × FastWitness) := [(r1888,⟨67,42,42⟩),(r1889,⟨67,42,42⟩),(r1890,⟨67,42,42⟩),(r1891,⟨67,42,42⟩),(r1892,⟨67,42,42⟩),(r1893,⟨67,42,42⟩),(r1894,⟨67,42,42⟩),(r1895,⟨67,42,42⟩)]
theorem checked236 : fastCheckList band b236=true := by decide +kernel

def b237 : List (Rectangle × FastWitness) := [(r1896,⟨67,42,42⟩),(r1897,⟨67,42,42⟩),(r1898,⟨67,42,42⟩),(r1899,⟨67,42,42⟩),(r1900,⟨67,42,42⟩),(r1901,⟨67,42,42⟩),(r1902,⟨67,42,42⟩),(r1903,⟨67,42,42⟩)]
theorem checked237 : fastCheckList band b237=true := by decide +kernel

def b238 : List (Rectangle × FastWitness) := [(r1904,⟨67,42,42⟩),(r1905,⟨67,42,42⟩),(r1906,⟨67,42,42⟩),(r1907,⟨67,42,42⟩),(r1908,⟨67,42,42⟩),(r1909,⟨67,42,42⟩),(r1910,⟨67,42,42⟩),(r1911,⟨67,42,42⟩)]
theorem checked238 : fastCheckList band b238=true := by decide +kernel

def b239 : List (Rectangle × FastWitness) := [(r1912,⟨67,42,42⟩),(r1913,⟨67,42,42⟩),(r1914,⟨67,42,42⟩),(r1915,⟨67,42,42⟩),(r1916,⟨67,42,42⟩),(r1917,⟨67,42,42⟩),(r1918,⟨67,42,42⟩),(r1919,⟨67,42,42⟩)]
theorem checked239 : fastCheckList band b239=true := by decide +kernel

def b240 : List (Rectangle × FastWitness) := [(r1920,⟨67,42,42⟩),(r1921,⟨67,42,42⟩),(r1922,⟨67,42,42⟩),(r1923,⟨67,42,42⟩),(r1924,⟨67,42,42⟩),(r1925,⟨67,42,42⟩),(r1926,⟨67,42,42⟩),(r1927,⟨67,42,42⟩)]
theorem checked240 : fastCheckList band b240=true := by decide +kernel

def b241 : List (Rectangle × FastWitness) := [(r1928,⟨67,42,42⟩),(r1929,⟨67,42,42⟩),(r1930,⟨67,42,42⟩),(r1931,⟨67,42,42⟩),(r1932,⟨67,42,42⟩),(r1933,⟨67,42,42⟩),(r1934,⟨67,42,42⟩),(r1935,⟨67,42,42⟩)]
theorem checked241 : fastCheckList band b241=true := by decide +kernel

def b242 : List (Rectangle × FastWitness) := [(r1936,⟨67,42,42⟩),(r1937,⟨67,42,42⟩),(r1938,⟨67,42,42⟩),(r1939,⟨67,42,42⟩),(r1940,⟨67,42,42⟩),(r1941,⟨67,42,42⟩),(r1942,⟨67,42,42⟩),(r1943,⟨67,42,42⟩)]
theorem checked242 : fastCheckList band b242=true := by decide +kernel

def b243 : List (Rectangle × FastWitness) := [(r1944,⟨67,42,42⟩),(r1945,⟨67,42,42⟩),(r1946,⟨67,42,42⟩),(r1947,⟨67,42,42⟩),(r1948,⟨67,42,42⟩),(r1949,⟨67,42,42⟩),(r1950,⟨67,42,42⟩),(r1951,⟨67,42,42⟩)]
theorem checked243 : fastCheckList band b243=true := by decide +kernel

def b244 : List (Rectangle × FastWitness) := [(r1952,⟨67,42,42⟩),(r1953,⟨67,42,42⟩),(r1954,⟨67,42,42⟩),(r1955,⟨67,42,42⟩),(r1956,⟨67,42,42⟩),(r1957,⟨67,42,42⟩),(r1958,⟨67,42,42⟩),(r1959,⟨67,42,42⟩)]
theorem checked244 : fastCheckList band b244=true := by decide +kernel

def b245 : List (Rectangle × FastWitness) := [(r1960,⟨67,42,42⟩),(r1961,⟨67,42,42⟩),(r1962,⟨67,42,42⟩),(r1963,⟨67,42,42⟩),(r1964,⟨67,42,42⟩),(r1965,⟨67,42,42⟩),(r1966,⟨67,42,42⟩),(r1967,⟨67,42,42⟩)]
theorem checked245 : fastCheckList band b245=true := by decide +kernel

def b246 : List (Rectangle × FastWitness) := [(r1968,⟨67,42,42⟩),(r1969,⟨67,42,42⟩),(r1970,⟨67,42,42⟩),(r1971,⟨67,42,42⟩),(r1972,⟨67,42,42⟩),(r1973,⟨67,42,42⟩),(r1974,⟨67,42,42⟩),(r1975,⟨67,42,42⟩)]
theorem checked246 : fastCheckList band b246=true := by decide +kernel

def b247 : List (Rectangle × FastWitness) := [(r1976,⟨67,42,42⟩),(r1977,⟨67,42,42⟩),(r1978,⟨67,42,42⟩),(r1979,⟨67,42,42⟩),(r1980,⟨67,42,42⟩),(r1981,⟨67,42,42⟩),(r1982,⟨67,42,42⟩),(r1983,⟨67,42,42⟩)]
theorem checked247 : fastCheckList band b247=true := by decide +kernel

def b248 : List (Rectangle × FastWitness) := [(r1984,⟨67,42,42⟩),(r1985,⟨67,42,42⟩),(r1986,⟨67,42,42⟩),(r1987,⟨67,42,42⟩),(r1988,⟨67,42,42⟩),(r1989,⟨67,42,42⟩),(r1990,⟨67,42,42⟩),(r1991,⟨67,42,42⟩)]
theorem checked248 : fastCheckList band b248=true := by decide +kernel

def b249 : List (Rectangle × FastWitness) := [(r1992,⟨67,42,42⟩),(r1993,⟨67,42,42⟩),(r1994,⟨67,42,42⟩),(r1995,⟨67,42,42⟩),(r1996,⟨67,42,42⟩),(r1997,⟨67,42,42⟩),(r1998,⟨67,42,42⟩),(r1999,⟨67,42,42⟩)]
theorem checked249 : fastCheckList band b249=true := by decide +kernel

def b250 : List (Rectangle × FastWitness) := [(r2000,⟨67,42,42⟩),(r2001,⟨67,42,42⟩),(r2002,⟨67,42,42⟩),(r2003,⟨67,42,42⟩),(r2004,⟨67,42,42⟩),(r2005,⟨67,42,42⟩),(r2006,⟨67,42,42⟩),(r2007,⟨67,42,42⟩)]
theorem checked250 : fastCheckList band b250=true := by decide +kernel

def b251 : List (Rectangle × FastWitness) := [(r2008,⟨67,42,42⟩),(r2009,⟨67,42,42⟩),(r2010,⟨67,42,42⟩),(r2011,⟨67,42,42⟩),(r2012,⟨67,42,42⟩),(r2013,⟨67,42,42⟩),(r2014,⟨67,42,42⟩),(r2015,⟨67,42,43⟩)]
theorem checked251 : fastCheckList band b251=true := by decide +kernel

def b252 : List (Rectangle × FastWitness) := [(r2016,⟨67,42,43⟩),(r2017,⟨67,43,43⟩),(r2018,⟨67,43,43⟩),(r2019,⟨67,43,43⟩),(r2020,⟨67,43,43⟩),(r2021,⟨67,43,43⟩),(r2022,⟨67,43,43⟩),(r2023,⟨67,43,43⟩)]
theorem checked252 : fastCheckList band b252=true := by decide +kernel

def b253 : List (Rectangle × FastWitness) := [(r2024,⟨67,43,43⟩),(r2025,⟨67,43,43⟩),(r2026,⟨67,43,43⟩),(r2027,⟨67,43,43⟩),(r2028,⟨67,43,43⟩),(r2029,⟨67,43,43⟩),(r2030,⟨67,43,43⟩),(r2031,⟨67,43,43⟩)]
theorem checked253 : fastCheckList band b253=true := by decide +kernel

def b254 : List (Rectangle × FastWitness) := [(r2032,⟨67,43,43⟩),(r2033,⟨67,43,43⟩),(r2034,⟨67,43,43⟩),(r2035,⟨67,43,43⟩),(r2036,⟨67,43,43⟩),(r2037,⟨67,43,43⟩),(r2038,⟨67,43,43⟩),(r2039,⟨67,43,43⟩)]
theorem checked254 : fastCheckList band b254=true := by decide +kernel

def b255 : List (Rectangle × FastWitness) := [(r2040,⟨67,43,43⟩),(r2041,⟨67,43,43⟩),(r2042,⟨67,43,43⟩),(r2043,⟨67,43,43⟩),(r2044,⟨67,43,43⟩),(r2045,⟨67,43,43⟩),(r2046,⟨67,43,43⟩),(r2047,⟨67,43,43⟩)]
theorem checked255 : fastCheckList band b255=true := by decide +kernel

end
end ProximityPrize.SubmissionLower.RelativeCertR13B54T3429To3499Fast


