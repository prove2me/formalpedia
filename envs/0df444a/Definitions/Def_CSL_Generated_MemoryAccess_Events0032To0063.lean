-- Prove2me | Definitions.Def_CSL_Generated_MemoryAccess_Events0032To0063
-- name    : CSL_Generated_MemoryAccess_Events0032To0063
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:34:56.491619+00:00
-- url     : https://prove2.me/theorems/92b722bc-4657-44c7-b497-b2daa3579dde
-- title:
--   Coded sorting library: Generated / MemoryAccess / Events0032To0063
-- statement:
--   Module `CodedSorting.Generated.MemoryAccess.Events0032To0063` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Generated.MemoryAccess.Events0032To0063

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_MemoryAccess_PhysicalFrameEventChunkData
import Definitions.Def_CSL_Generated_MemoryAccess_Base

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Literal sparse visit certificate for the exact chunk 1. -/
def forwardVisitTree001 : VisitTree := (VisitTree.branch 409 (VisitTree.branch 300 (VisitTree.branch 245 (VisitTree.branch 170 (VisitTree.branch 156 (VisitTree.branch 149 (VisitTree.branch 146 (VisitTree.branch 144 (VisitTree.leaf 143 [0]) (VisitTree.branch 145 (VisitTree.leaf 144 [0]) (VisitTree.leaf 145 [0]))) (VisitTree.branch 147 (VisitTree.leaf 146 [0]) (VisitTree.branch 148 (VisitTree.leaf 147 [0]) (VisitTree.leaf 148 [0])))) (VisitTree.branch 152 (VisitTree.branch 150 (VisitTree.leaf 149 [0]) (VisitTree.branch 151 (VisitTree.leaf 150 [0]) (VisitTree.leaf 151 [0]))) (VisitTree.branch 154 (VisitTree.branch 153 (VisitTree.leaf 152 [0]) (VisitTree.leaf 153 [0])) (VisitTree.branch 155 (VisitTree.leaf 154 [0]) (VisitTree.leaf 155 [0]))))) (VisitTree.branch 163 (VisitTree.branch 159 (VisitTree.branch 157 (VisitTree.leaf 156 [0]) (VisitTree.branch 158 (VisitTree.leaf 157 [0]) (VisitTree.leaf 158 [0]))) (VisitTree.branch 161 (VisitTree.branch 160 (VisitTree.leaf 159 [0]) (VisitTree.leaf 160 [0])) (VisitTree.branch 162 (VisitTree.leaf 161 [0]) (VisitTree.leaf 162 [0])))) (VisitTree.branch 166 (VisitTree.branch 164 (VisitTree.leaf 163 [0]) (VisitTree.branch 165 (VisitTree.leaf 164 [0]) (VisitTree.leaf 165 [0]))) (VisitTree.branch 168 (VisitTree.branch 167 (VisitTree.leaf 166 [0]) (VisitTree.leaf 167 [0])) (VisitTree.branch 169 (VisitTree.leaf 168 [0]) (VisitTree.leaf 169 [0])))))) (VisitTree.branch 230 (VisitTree.branch 223 (VisitTree.branch 173 (VisitTree.branch 171 (VisitTree.leaf 170 [0]) (VisitTree.branch 172 (VisitTree.leaf 171 [0]) (VisitTree.leaf 172 [0]))) (VisitTree.branch 174 (VisitTree.leaf 173 [0]) (VisitTree.branch 222 (VisitTree.leaf 174 [0]) (VisitTree.leaf 222 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 226 (VisitTree.branch 224 (VisitTree.leaf 223 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 225 (VisitTree.leaf 224 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 225 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 228 (VisitTree.branch 227 (VisitTree.leaf 226 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 227 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 229 (VisitTree.leaf 228 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 229 [0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 238 (VisitTree.branch 233 (VisitTree.branch 231 (VisitTree.leaf 230 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 232 (VisitTree.leaf 231 [0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 232 [0, 0]))) (VisitTree.branch 235 (VisitTree.branch 234 (VisitTree.leaf 233 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 234 [0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 237 (VisitTree.leaf 235 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 237 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 241 (VisitTree.branch 239 (VisitTree.leaf 238 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 240 (VisitTree.leaf 239 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 240 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 243 (VisitTree.branch 242 (VisitTree.leaf 241 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 242 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 244 (VisitTree.leaf 243 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 244 [0, 0, 0]))))))) (VisitTree.branch 272 (VisitTree.branch 258 (VisitTree.branch 251 (VisitTree.branch 248 (VisitTree.branch 246 (VisitTree.leaf 245 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 247 (VisitTree.leaf 246 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 247 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 249 (VisitTree.leaf 248 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 250 (VisitTree.leaf 249 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 250 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 254 (VisitTree.branch 252 (VisitTree.leaf 251 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 253 (VisitTree.leaf 252 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 253 [0, 0, 0, 0, 0, 0]))) (VisitTree.branch 256 (VisitTree.branch 255 (VisitTree.leaf 254 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 255 [0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 257 (VisitTree.leaf 256 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 257 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 265 (VisitTree.branch 261 (VisitTree.branch 259 (VisitTree.leaf 258 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 260 (VisitTree.leaf 259 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 260 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 263 (VisitTree.branch 262 (VisitTree.leaf 261 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 262 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 264 (VisitTree.leaf 263 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 264 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 268 (VisitTree.branch 266 (VisitTree.leaf 265 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 267 (VisitTree.leaf 266 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 267 [0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 270 (VisitTree.branch 269 (VisitTree.leaf 268 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 269 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 271 (VisitTree.leaf 270 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 271 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 286 (VisitTree.branch 279 (VisitTree.branch 275 (VisitTree.branch 273 (VisitTree.leaf 272 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 274 (VisitTree.leaf 273 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 274 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 277 (VisitTree.branch 276 (VisitTree.leaf 275 [0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 276 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 278 (VisitTree.leaf 277 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 278 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 282 (VisitTree.branch 280 (VisitTree.leaf 279 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 281 (VisitTree.leaf 280 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 281 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 284 (VisitTree.branch 283 (VisitTree.leaf 282 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 283 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 285 (VisitTree.leaf 284 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 285 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 293 (VisitTree.branch 289 (VisitTree.branch 287 (VisitTree.leaf 286 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 288 (VisitTree.leaf 287 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 288 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 291 (VisitTree.branch 290 (VisitTree.leaf 289 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 290 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 292 (VisitTree.leaf 291 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 292 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 296 (VisitTree.branch 294 (VisitTree.leaf 293 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 295 (VisitTree.leaf 294 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 295 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 298 (VisitTree.branch 297 (VisitTree.leaf 296 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 297 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 299 (VisitTree.leaf 298 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 299 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))))) (VisitTree.branch 354 (VisitTree.branch 327 (VisitTree.branch 313 (VisitTree.branch 306 (VisitTree.branch 303 (VisitTree.branch 301 (VisitTree.leaf 300 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 302 (VisitTree.leaf 301 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 302 [0, 0]))) (VisitTree.branch 304 (VisitTree.leaf 303 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 305 (VisitTree.leaf 304 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 305 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 309 (VisitTree.branch 307 (VisitTree.leaf 306 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 308 (VisitTree.leaf 307 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 308 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 311 (VisitTree.branch 310 (VisitTree.leaf 309 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 310 [0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 312 (VisitTree.leaf 311 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 312 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 320 (VisitTree.branch 316 (VisitTree.branch 314 (VisitTree.leaf 313 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 315 (VisitTree.leaf 314 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 315 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 318 (VisitTree.branch 317 (VisitTree.leaf 316 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 317 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 319 (VisitTree.leaf 318 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 319 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 323 (VisitTree.branch 321 (VisitTree.leaf 320 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 322 (VisitTree.leaf 321 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 322 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 325 (VisitTree.branch 324 (VisitTree.leaf 323 [0, 0, 0, 0, 0]) (VisitTree.leaf 324 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 326 (VisitTree.leaf 325 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 326 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 340 (VisitTree.branch 333 (VisitTree.branch 330 (VisitTree.branch 328 (VisitTree.leaf 327 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 329 (VisitTree.leaf 328 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 329 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 331 (VisitTree.leaf 330 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 332 (VisitTree.leaf 331 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 332 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 336 (VisitTree.branch 334 (VisitTree.leaf 333 [0, 0, 0, 0, 0]) (VisitTree.branch 335 (VisitTree.leaf 334 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 335 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 338 (VisitTree.branch 337 (VisitTree.leaf 336 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 337 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 339 (VisitTree.leaf 338 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 339 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 347 (VisitTree.branch 343 (VisitTree.branch 341 (VisitTree.leaf 340 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 342 (VisitTree.leaf 341 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 342 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 345 (VisitTree.branch 344 (VisitTree.leaf 343 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 344 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 346 (VisitTree.leaf 345 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 346 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 350 (VisitTree.branch 348 (VisitTree.leaf 347 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 349 (VisitTree.leaf 348 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 349 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 352 (VisitTree.branch 351 (VisitTree.leaf 350 [0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 351 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 353 (VisitTree.leaf 352 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 353 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))) (VisitTree.branch 381 (VisitTree.branch 367 (VisitTree.branch 360 (VisitTree.branch 357 (VisitTree.branch 355 (VisitTree.leaf 354 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 356 (VisitTree.leaf 355 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 356 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 358 (VisitTree.leaf 357 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 359 (VisitTree.leaf 358 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 359 [0, 0, 0, 0])))) (VisitTree.branch 363 (VisitTree.branch 361 (VisitTree.leaf 360 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 362 (VisitTree.leaf 361 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 362 [0, 0, 0, 0, 0]))) (VisitTree.branch 365 (VisitTree.branch 364 (VisitTree.leaf 363 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 364 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 366 (VisitTree.leaf 365 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 366 [0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 374 (VisitTree.branch 370 (VisitTree.branch 368 (VisitTree.leaf 367 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 369 (VisitTree.leaf 368 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 369 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 372 (VisitTree.branch 371 (VisitTree.leaf 370 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 371 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 373 (VisitTree.leaf 372 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 373 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 377 (VisitTree.branch 375 (VisitTree.leaf 374 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 376 (VisitTree.leaf 375 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 376 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 379 (VisitTree.branch 378 (VisitTree.leaf 377 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 378 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 380 (VisitTree.leaf 379 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 380 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 395 (VisitTree.branch 388 (VisitTree.branch 384 (VisitTree.branch 382 (VisitTree.leaf 381 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 383 (VisitTree.leaf 382 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 383 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 386 (VisitTree.branch 385 (VisitTree.leaf 384 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 385 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 387 (VisitTree.leaf 386 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 387 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 391 (VisitTree.branch 389 (VisitTree.leaf 388 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 390 (VisitTree.leaf 389 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 390 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 393 (VisitTree.branch 392 (VisitTree.leaf 391 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 392 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 394 (VisitTree.leaf 393 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 394 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 402 (VisitTree.branch 398 (VisitTree.branch 396 (VisitTree.leaf 395 [0, 0, 0, 0, 0, 0]) (VisitTree.branch 397 (VisitTree.leaf 396 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 397 [0, 0, 0, 0, 0, 0]))) (VisitTree.branch 400 (VisitTree.branch 399 (VisitTree.leaf 398 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 399 [0, 0, 0, 0, 0, 0])) (VisitTree.branch 401 (VisitTree.leaf 400 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 401 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 405 (VisitTree.branch 403 (VisitTree.leaf 402 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 404 (VisitTree.leaf 403 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 404 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 407 (VisitTree.branch 406 (VisitTree.leaf 405 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 406 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 408 (VisitTree.leaf 407 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 408 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))))) (VisitTree.branch 528 (VisitTree.branch 464 (VisitTree.branch 436 (VisitTree.branch 422 (VisitTree.branch 415 (VisitTree.branch 412 (VisitTree.branch 410 (VisitTree.leaf 409 [0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 411 (VisitTree.leaf 410 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 411 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 413 (VisitTree.leaf 412 [0, 0, 0, 0, 0, 0]) (VisitTree.branch 414 (VisitTree.leaf 413 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 414 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 418 (VisitTree.branch 416 (VisitTree.leaf 415 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 417 (VisitTree.leaf 416 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 417 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 420 (VisitTree.branch 419 (VisitTree.leaf 418 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 419 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 421 (VisitTree.leaf 420 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 421 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 429 (VisitTree.branch 425 (VisitTree.branch 423 (VisitTree.leaf 422 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 424 (VisitTree.leaf 423 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 424 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 427 (VisitTree.branch 426 (VisitTree.leaf 425 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 426 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 428 (VisitTree.leaf 427 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 428 [0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 432 (VisitTree.branch 430 (VisitTree.leaf 429 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 431 (VisitTree.leaf 430 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 431 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 434 (VisitTree.branch 433 (VisitTree.leaf 432 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 433 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 435 (VisitTree.leaf 434 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 435 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 449 (VisitTree.branch 442 (VisitTree.branch 439 (VisitTree.branch 437 (VisitTree.leaf 436 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 438 (VisitTree.leaf 437 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 438 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 440 (VisitTree.leaf 439 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 441 (VisitTree.leaf 440 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 441 [0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 445 (VisitTree.branch 443 (VisitTree.leaf 442 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 444 (VisitTree.leaf 443 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 444 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 447 (VisitTree.branch 446 (VisitTree.leaf 445 [0, 0, 0, 0, 0]) (VisitTree.leaf 446 [0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 448 (VisitTree.leaf 447 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 448 [0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 456 (VisitTree.branch 452 (VisitTree.branch 450 (VisitTree.leaf 449 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 451 (VisitTree.leaf 450 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 451 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 454 (VisitTree.branch 453 (VisitTree.leaf 452 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 453 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 455 (VisitTree.leaf 454 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 455 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 460 (VisitTree.branch 458 (VisitTree.leaf 456 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 459 (VisitTree.leaf 458 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 459 [0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 462 (VisitTree.branch 461 (VisitTree.leaf 460 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 461 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 463 (VisitTree.leaf 462 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 463 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))) (VisitTree.branch 494 (VisitTree.branch 477 (VisitTree.branch 470 (VisitTree.branch 467 (VisitTree.branch 465 (VisitTree.leaf 464 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 466 (VisitTree.leaf 465 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 466 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 468 (VisitTree.leaf 467 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 469 (VisitTree.leaf 468 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 469 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 473 (VisitTree.branch 471 (VisitTree.leaf 470 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 472 (VisitTree.leaf 471 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 472 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 475 (VisitTree.branch 474 (VisitTree.leaf 473 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 474 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 476 (VisitTree.leaf 475 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 476 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 487 (VisitTree.branch 480 (VisitTree.branch 478 (VisitTree.leaf 477 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 479 (VisitTree.leaf 478 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 479 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 485 (VisitTree.branch 484 (VisitTree.leaf 480 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 484 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 486 (VisitTree.leaf 485 [0, 0, 0, 0, 0, 0]) (VisitTree.leaf 486 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 490 (VisitTree.branch 488 (VisitTree.leaf 487 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 489 (VisitTree.leaf 488 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 489 [0, 0, 0]))) (VisitTree.branch 492 (VisitTree.branch 491 (VisitTree.leaf 490 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 491 [0, 0, 0])) (VisitTree.branch 493 (VisitTree.leaf 492 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 493 [0, 0, 0, 0])))))) (VisitTree.branch 511 (VisitTree.branch 504 (VisitTree.branch 497 (VisitTree.branch 495 (VisitTree.leaf 494 [0, 0, 0]) (VisitTree.branch 496 (VisitTree.leaf 495 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 496 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 499 (VisitTree.branch 498 (VisitTree.leaf 497 [0, 0]) (VisitTree.leaf 498 [0, 0, 0, 0, 0])) (VisitTree.branch 501 (VisitTree.leaf 499 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 501 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 507 (VisitTree.branch 505 (VisitTree.leaf 504 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 506 (VisitTree.leaf 505 [0, 0]) (VisitTree.leaf 506 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 509 (VisitTree.branch 508 (VisitTree.leaf 507 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 508 [0, 0])) (VisitTree.branch 510 (VisitTree.leaf 509 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 510 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 518 (VisitTree.branch 514 (VisitTree.branch 512 (VisitTree.leaf 511 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 513 (VisitTree.leaf 512 [0, 0]) (VisitTree.leaf 513 [0, 0]))) (VisitTree.branch 516 (VisitTree.branch 515 (VisitTree.leaf 514 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 515 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 517 (VisitTree.leaf 516 [0, 0, 0, 0]) (VisitTree.leaf 517 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 524 (VisitTree.branch 522 (VisitTree.leaf 518 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 523 (VisitTree.leaf 522 [0, 0, 0, 0]) (VisitTree.leaf 523 [0, 0, 0, 0]))) (VisitTree.branch 526 (VisitTree.branch 525 (VisitTree.leaf 524 [0, 0, 0]) (VisitTree.leaf 525 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 527 (VisitTree.leaf 526 [0, 0]) (VisitTree.leaf 527 [0, 0])))))))) (VisitTree.branch 595 (VisitTree.branch 560 (VisitTree.branch 543 (VisitTree.branch 534 (VisitTree.branch 531 (VisitTree.branch 529 (VisitTree.leaf 528 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 530 (VisitTree.leaf 529 [0]) (VisitTree.leaf 530 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 532 (VisitTree.leaf 531 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 533 (VisitTree.leaf 532 [0, 0, 0]) (VisitTree.leaf 533 [0, 0, 0])))) (VisitTree.branch 538 (VisitTree.branch 535 (VisitTree.leaf 534 [0, 0, 0, 0]) (VisitTree.branch 536 (VisitTree.leaf 535 [0, 0, 0, 0, 0]) (VisitTree.leaf 536 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 541 (VisitTree.branch 540 (VisitTree.leaf 538 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 540 [0, 0, 0, 0])) (VisitTree.branch 542 (VisitTree.leaf 541 [0, 0, 0]) (VisitTree.leaf 542 [0, 0, 0]))))) (VisitTree.branch 550 (VisitTree.branch 546 (VisitTree.branch 544 (VisitTree.leaf 543 [0, 0]) (VisitTree.branch 545 (VisitTree.leaf 544 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 545 [0]))) (VisitTree.branch 548 (VisitTree.branch 547 (VisitTree.leaf 546 [0, 0, 0, 0]) (VisitTree.leaf 547 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 549 (VisitTree.leaf 548 [0, 0]) (VisitTree.leaf 549 [0, 0, 0])))) (VisitTree.branch 553 (VisitTree.branch 551 (VisitTree.leaf 550 [0]) (VisitTree.branch 552 (VisitTree.leaf 551 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 552 [0, 0]))) (VisitTree.branch 558 (VisitTree.branch 554 (VisitTree.leaf 553 [0, 0, 0, 0]) (VisitTree.leaf 554 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 559 (VisitTree.leaf 558 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 559 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 578 (VisitTree.branch 567 (VisitTree.branch 563 (VisitTree.branch 561 (VisitTree.leaf 560 [0, 0]) (VisitTree.branch 562 (VisitTree.leaf 561 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 562 [0, 0]))) (VisitTree.branch 565 (VisitTree.branch 564 (VisitTree.leaf 563 [0, 0, 0]) (VisitTree.leaf 564 [0, 0])) (VisitTree.branch 566 (VisitTree.leaf 565 [0, 0]) (VisitTree.leaf 566 [0, 0])))) (VisitTree.branch 570 (VisitTree.branch 568 (VisitTree.leaf 567 [0, 0, 0]) (VisitTree.branch 569 (VisitTree.leaf 568 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 569 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 576 (VisitTree.branch 571 (VisitTree.leaf 570 [0, 0]) (VisitTree.leaf 571 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 577 (VisitTree.leaf 576 [0, 0, 0, 0, 0]) (VisitTree.leaf 577 [0, 0]))))) (VisitTree.branch 585 (VisitTree.branch 581 (VisitTree.branch 579 (VisitTree.leaf 578 [0, 0]) (VisitTree.branch 580 (VisitTree.leaf 579 [0, 0]) (VisitTree.leaf 580 [0, 0, 0]))) (VisitTree.branch 583 (VisitTree.branch 582 (VisitTree.leaf 581 [0, 0]) (VisitTree.leaf 582 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 584 (VisitTree.leaf 583 [0, 0, 0]) (VisitTree.leaf 584 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 588 (VisitTree.branch 586 (VisitTree.leaf 585 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 587 (VisitTree.leaf 586 [0, 0, 0]) (VisitTree.leaf 587 [0]))) (VisitTree.branch 593 (VisitTree.branch 589 (VisitTree.leaf 588 [0, 0]) (VisitTree.leaf 589 [0, 0, 0])) (VisitTree.branch 594 (VisitTree.leaf 593 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 594 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))))) (VisitTree.branch 626 (VisitTree.branch 609 (VisitTree.branch 601 (VisitTree.branch 598 (VisitTree.branch 596 (VisitTree.leaf 595 [0, 0, 0, 0]) (VisitTree.branch 597 (VisitTree.leaf 596 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 597 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 599 (VisitTree.leaf 598 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 600 (VisitTree.leaf 599 [0, 0, 0]) (VisitTree.leaf 600 [0])))) (VisitTree.branch 604 (VisitTree.branch 602 (VisitTree.leaf 601 [0, 0]) (VisitTree.branch 603 (VisitTree.leaf 602 [0, 0, 0]) (VisitTree.leaf 603 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 606 (VisitTree.branch 605 (VisitTree.leaf 604 [0, 0, 0, 0]) (VisitTree.leaf 605 [0, 0, 0])) (VisitTree.branch 608 (VisitTree.leaf 606 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 608 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 617 (VisitTree.branch 612 (VisitTree.branch 610 (VisitTree.leaf 609 [0, 0, 0, 0]) (VisitTree.branch 611 (VisitTree.leaf 610 [0, 0, 0]) (VisitTree.leaf 611 [0, 0, 0]))) (VisitTree.branch 615 (VisitTree.branch 614 (VisitTree.leaf 612 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 614 [0, 0, 0, 0])) (VisitTree.branch 616 (VisitTree.leaf 615 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 616 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))) (VisitTree.branch 622 (VisitTree.branch 620 (VisitTree.leaf 617 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 621 (VisitTree.leaf 620 [0, 0, 0, 0]) (VisitTree.leaf 621 [0, 0, 0, 0]))) (VisitTree.branch 624 (VisitTree.branch 623 (VisitTree.leaf 622 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 623 [0, 0, 0, 0])) (VisitTree.branch 625 (VisitTree.leaf 624 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 625 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])))))) (VisitTree.branch 644 (VisitTree.branch 634 (VisitTree.branch 629 (VisitTree.branch 627 (VisitTree.leaf 626 [0, 0, 0]) (VisitTree.branch 628 (VisitTree.leaf 627 [0, 0, 0]) (VisitTree.leaf 628 [0, 0, 0, 0]))) (VisitTree.branch 632 (VisitTree.branch 631 (VisitTree.leaf 629 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 631 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 633 (VisitTree.leaf 632 [0, 0, 0, 0]) (VisitTree.leaf 633 [0, 0, 0, 0])))) (VisitTree.branch 639 (VisitTree.branch 635 (VisitTree.leaf 634 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 638 (VisitTree.leaf 635 [0, 0, 0, 0]) (VisitTree.leaf 638 [0, 0, 0, 0]))) (VisitTree.branch 641 (VisitTree.branch 640 (VisitTree.leaf 639 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 640 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 643 (VisitTree.leaf 641 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 643 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))))) (VisitTree.branch 654 (VisitTree.branch 650 (VisitTree.branch 648 (VisitTree.leaf 644 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.branch 649 (VisitTree.leaf 648 [0, 0, 0]) (VisitTree.leaf 649 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 652 (VisitTree.branch 651 (VisitTree.leaf 650 [0, 0]) (VisitTree.leaf 651 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 653 (VisitTree.leaf 652 [0, 0, 0]) (VisitTree.leaf 653 [0, 0, 0, 0])))) (VisitTree.branch 657 (VisitTree.branch 655 (VisitTree.leaf 654 [0, 0]) (VisitTree.branch 656 (VisitTree.leaf 655 [0, 0, 0]) (VisitTree.leaf 656 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]))) (VisitTree.branch 659 (VisitTree.branch 658 (VisitTree.leaf 657 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) (VisitTree.leaf 658 [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])) (VisitTree.branch 660 (VisitTree.leaf 659 [0, 0, 0, 0]) (VisitTree.leaf 660 [0, 0]))))))))))

def fastForwardChunkVisits001 (r : Nat) : List Nat :=
  forwardVisitTree001.lookup r

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem covered001 :
    visitsCovered forwardEventChunk001 forwardVisitTree001 = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part000 :
    ([143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part001 :
    ([159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part002 :
    ([222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 237, 238] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part003 :
    ([239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part004 :
    ([255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part005 :
    ([271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part006 :
    ([287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part007 :
    ([303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part008 :
    ([319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part009 :
    ([335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part010 :
    ([351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part011 :
    ([367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part012 :
    ([383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part013 :
    ([399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part014 :
    ([415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part015 :
    ([431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part016 :
    ([447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 458, 459, 460, 461, 462, 463] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part017 :
    ([464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part018 :
    ([480, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part019 :
    ([499, 501, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part020 :
    ([518, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part021 :
    ([538, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part022 :
    ([558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 576, 577] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part023 :
    ([578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 593, 594, 595, 596] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part024 :
    ([597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 608, 609, 610, 611, 612, 614] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part025 :
    ([615, 616, 617, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 631, 632, 633] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part026 :
    ([634, 635, 638, 639, 640, 641, 643, 644, 648, 649, 650, 651, 652, 653, 654, 655] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem checked001Part027 :
    ([656, 657, 658, 659, 660] : List Nat).all (fun r => eventVisits r forwardEventChunk001 ==
      forwardVisitTree001.lookup r) = true := by
  decide +kernel

end
end CSL.Construction.PhysicalFramePaths

namespace CSL.Construction.PhysicalFramePaths
noncomputable section
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem keys_eq001 : forwardVisitTree001.keys = [143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158] ++ [159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174] ++ [222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 237, 238] ++ [239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254] ++ [255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270] ++ [271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286] ++ [287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302] ++ [303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318] ++ [319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334] ++ [335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350] ++ [351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366] ++ [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382] ++ [383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398] ++ [399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414] ++ [415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430] ++ [431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446] ++ [447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 458, 459, 460, 461, 462, 463] ++ [464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479] ++ [480, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498] ++ [499, 501, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517] ++ [518, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536] ++ [538, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554] ++ [558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 576, 577] ++ [578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 593, 594, 595, 596] ++ [597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 608, 609, 610, 611, 612, 614] ++ [615, 616, 617, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 631, 632, 633] ++ [634, 635, 638, 639, 640, 641, 643, 644, 648, 649, 650, 651, 652, 653, 654, 655] ++ [656, 657, 658, 659, 660] := by rfl

private theorem checked001 :
    visitsChecked forwardEventChunk001 forwardVisitTree001 = true := by
  simp only [visitsChecked, keys_eq001, List.all_append,
    checked001Part000, checked001Part001, checked001Part002, checked001Part003, checked001Part004, checked001Part005, checked001Part006, checked001Part007, checked001Part008, checked001Part009, checked001Part010, checked001Part011, checked001Part012, checked001Part013, checked001Part014, checked001Part015, checked001Part016, checked001Part017, checked001Part018, checked001Part019, checked001Part020, checked001Part021, checked001Part022, checked001Part023, checked001Part024, checked001Part025, checked001Part026, checked001Part027, Bool.true_and]

theorem eventVisits_forwardChunk001 (r : Nat) :
    eventVisits r forwardEventChunk001 = fastForwardChunkVisits001 r :=
  eventVisits_of_tree _ _ covered001 checked001 r

end
end CSL.Construction.PhysicalFramePaths

#print axioms CSL.Construction.PhysicalFramePaths.eventVisits_forwardChunk001


